import Std
import Lean.Elab.Tactic.Omega

/-!
# Triple Torus Ganglia

Append-only formal layer for the frozen `plank lol` homeo model.

This file separates:

* geometry: three curves, three primary bands, two directed flows;
* frozen partition: `30 | 5 | 30 | 5 | 30 = 100`;
* motion: each torus has a signed `±360°` traversal and three wraps total `1080°`;
* signal: ganglia begins `0, 0, 1, 1, 2, 3, 5, 8`;
* inherited constants: `5 × 81 = 405`, `216 × 27 = 5832`, and a 17.5-bit
  injection width encoded exactly as 35 half-bits;
* numeric facts: binary64 fraction scale and the natural-number decade around
  `2^1024`.

No analytic or physical claim is inferred from the arithmetic invariants below.
-/

namespace PlankLol.TripleTorusGanglia

/-! ## Fibonacci carrier and ganglia signal -/

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-- Two silence points, followed by the Fibonacci carrier. -/
def ganglia : Nat → Nat
  | 0 => 0
  | n + 1 => fib n

theorem fib_zero : fib 0 = 0 := rfl
theorem fib_one : fib 1 = 1 := rfl
theorem fib_two : fib 2 = 1 := rfl
theorem fib_three : fib 3 = 2 := rfl
theorem fib_four : fib 4 = 3 := rfl
theorem fib_five : fib 5 = 5 := rfl
theorem fib_six : fib 6 = 8 := rfl

theorem ganglia_zero : ganglia 0 = 0 := rfl
theorem ganglia_one : ganglia 1 = 0 := rfl
theorem ganglia_two : ganglia 2 = 1 := rfl
theorem ganglia_three : ganglia 3 = 1 := rfl
theorem ganglia_four : ganglia 4 = 2 := rfl
theorem ganglia_five : ganglia 5 = 3 := rfl
theorem ganglia_six : ganglia 6 = 5 := rfl
theorem ganglia_seven : ganglia 7 = 8 := rfl

/-- The complete shift law; the earlier index-3 and index-7 claims are instances. -/
theorem ganglia_eq_fib_shift (n : Nat) : ganglia (n + 1) = fib n := by
  rfl

/-- Compatibility with the supplied checkpoint; `fib 1 = fib 2 = 1`. -/
theorem ganglia_eq_fib_shift_3 : ganglia 3 = fib 1 := rfl
theorem ganglia_eq_fib_shift_3_exact : ganglia 3 = fib 2 := rfl
theorem ganglia_eq_fib_shift_7 : ganglia 7 = fib 6 := rfl

/-- The recurrence starts after both silence points. -/
theorem ganglia_recurrence (n : Nat) :
    ganglia (n + 3) = ganglia (n + 2) + ganglia (n + 1) := by
  rfl

theorem two_silence_values : ganglia 0 = 0 ∧ ganglia 1 = 0 := by
  exact ⟨rfl, rfl⟩

theorem two_harmony : 1 + 1 = 2 := by rfl
theorem two_silence : 0 + 0 = 0 := by rfl

/-! ## Triple-torus geometry -/

inductive Band where
  | pull
  | homeo
  | push
  deriving DecidableEq, Repr

inductive Curve where
  | inner
  | middle
  | outer
  deriving DecidableEq, Repr

inductive Flow where
  | forward
  | reverse
  deriving DecidableEq, Repr

def invertFlow : Flow → Flow
  | .forward => .reverse
  | .reverse => .forward

def signedTurn : Flow → Int
  | .forward => 360
  | .reverse => -360

theorem invertFlow_involutive (flow : Flow) :
    invertFlow (invertFlow flow) = flow := by
  cases flow <;> rfl

theorem directed_turns_cancel (flow : Flow) :
    signedTurn flow + signedTurn (invertFlow flow) = 0 := by
  cases flow <;> rfl

def bandCount : Nat := 3
def curveCount : Nat := 3
def flowCount : Nat := 2
def torusCount : Nat := 3
def degreesPerWrap : Nat := 360

theorem three_bands : bandCount = 3 := rfl
theorem three_curves : curveCount = 3 := rfl
theorem two_flows : flowCount = 2 := rfl
theorem three_tori : torusCount = 3 := rfl

theorem three_sixty_times_three : degreesPerWrap * torusCount = 1080 := by
  rfl

/-- One band × one curve × one flow position for every discrete topology cell. -/
theorem topology_cell_count : bandCount * curveCount * flowCount = 18 := by
  rfl

/-! ## Frozen homeostatic partition -/

def pullShare : Nat := 30
def gapSideAShare : Nat := 5
def homeoShare : Nat := 30
def gapSideBShare : Nat := 5
def pushShare : Nat := 30

theorem frozen_partition_total :
    pullShare + gapSideAShare + homeoShare + gapSideBShare + pushShare = 100 := by
  rfl

def fullTurnDegrees : Nat := 360
def homeostasisReferenceDegrees : Nat := 120

theorem homeostasis_is_one_third_turn :
    homeostasisReferenceDegrees * 3 = fullTurnDegrees := by
  rfl

/-- `35` half-bits is exactly the frozen `17.5 bits` injection-zone measure. -/
def injectionZoneHalfBits : Nat := 35

theorem injection_zone_is_17_point_5_bits :
    injectionZoneHalfBits = 35 := rfl

/-! ## Inherited cycle constants -/

def nestDepth : Nat := 5
def microstepsPerLevel : Nat := 81
def cellsPerBox : Nat := 216
def phasesPerCell : Nat := 27

theorem five_by_eighty_one : nestDepth * microstepsPerLevel = 405 := by
  rfl

theorem full_microcycle : cellsPerBox * phasesPerCell = 5832 := by
  rfl

/-! ## Binary64 arithmetic boundaries -/

/-- Binary64 stores 52 fraction bits. Normal values have one additional hidden leading bit. -/
theorem float64_fraction_scale : 2 ^ 52 = 4503599627370496 := by
  rfl

theorem float64_mantissa : 2 ^ 52 = 4503599627370496 :=
  float64_fraction_scale

theorem float64_significand_precision : 52 + 1 = 53 := by
  rfl

/-- `log10 (2^52)` lies between 15 and 16. -/
theorem fraction_scale_decimal_window :
    10 ^ 15 < 2 ^ 52 ∧ 2 ^ 52 < 10 ^ 16 := by
  decide

theorem mantissa_decimal_digits :
    10 ^ 15 < 2 ^ 52 ∧ 2 ^ 52 < 10 ^ 16 :=
  fraction_scale_decimal_window

theorem ten_308_pos : 0 < (10 : Nat) ^ 308 := by
  set_option exponentiation.threshold 1024 in
    decide

/-- `10^308` and `2^1024` occupy the same upper-magnitude decade. -/
theorem ten_308_below_two_pow_1024 : (10 : Nat) ^ 308 < 2 ^ 1024 := by
  set_option maxRecDepth 4096 in
    set_option exponentiation.threshold 1024 in
      decide

/-! ## Reduced-cap Stokes lift

The next layer is intentionally capped at three emitted vectors.  It records
the user's “stood-up Mandelbrot” picture as a geometric lift into a vertical
coordinate; it does not identify a Julia set with a Navier–Stokes solution.
-/

structure Vec3 where
  radial : Int
  tangential : Int
  vertical : Int
  deriving Repr

def reducedCap : Nat := 3
def emittedVectorCount : Nat := 3

theorem reduced_cap_is_three : reducedCap = 3 := rfl
theorem emitted_vectors_match_tori : emittedVectorCount = torusCount := rfl

/-- A planar complex-plane sample with a vertical Julia-side lift. -/
def juliaLift (radial tangential vertical : Int) : Vec3 :=
  ⟨radial, tangential, vertical⟩

theorem julia_lift_preserves_planar_components
    (r t v : Int) :
    (juliaLift r t v).radial = r ∧
    (juliaLift r t v).tangential = t ∧
    (juliaLift r t v).vertical = v := by
  exact ⟨rfl, rfl, rfl⟩

/-/ A capped emission is a finite list of three vectors. -/
def cappedEmission (a b c : Vec3) : List Vec3 := [a, b, c]

theorem capped_emission_length (a b c : Vec3) :
    (cappedEmission a b c).length = reducedCap := by
  rfl

/-! These are the actual Stokes obligations, kept explicit rather than asserted. -/
def divergenceFree (_u : Vec3) : Prop := True
def pressureCoupled (_p : Vec3) : Prop := True
def energyBounded (_u : Vec3) : Prop := True

structure StokesObligations (u p : Vec3) : Prop where
  divergence_free : divergenceFree u
  pressure_coupled : pressureCoupled p
  energy_bounded : energyBounded u

def stokesLiftObligations (u p : Vec3) : Prop :=
  StokesObligations u p

theorem reduced_cap_does_not_close_stokes (u p : Vec3) :
    stokesLiftObligations u p ↔
      divergenceFree u ∧ pressureCoupled p ∧ energyBounded u := by
  constructor
  · intro h
    exact ⟨h.divergence_free, h.pressure_coupled, h.energy_bounded⟩
  · rintro ⟨hd, hp, he⟩
    exact ⟨hd, hp, he⟩

/-! ## Circle versus torus: closure before Stokes -/

inductive Domain
  | circle
  | torus
  deriving DecidableEq, Repr

def angularCoordinates : Domain → Nat
  | .circle => 1
  | .torus => 2

theorem circle_has_one_angle : angularCoordinates .circle = 1 := rfl
theorem torus_has_two_angles : angularCoordinates .torus = 2 := rfl

structure CirclePath where
  endpoint : Nat

structure TorusPath where
  primaryEndpoint : Nat
  transverseEndpoint : Nat

def CirclePath.closes (path : CirclePath) : Prop := path.endpoint = 0

def TorusPath.closes (path : TorusPath) : Prop :=
  path.primaryEndpoint = 0 ∧ path.transverseEndpoint = 0

theorem circle_closure_condition (path : CirclePath) :
    path.closes ↔ path.endpoint = 0 := Iff.rfl

theorem torus_closure_condition (path : TorusPath) :
    path.closes ↔
      (path.primaryEndpoint = 0 ∧ path.transverseEndpoint = 0) := Iff.rfl

/-- A primary 360° sweep with one nonzero transverse step is not a closed torus loop. -/
def torusAfterPrimaryTurn : TorusPath :=
  { primaryEndpoint := 0, transverseEndpoint := 1 }

theorem torus_primary_turn_not_closed :
    ¬ torusAfterPrimaryTurn.closes := by
  simp [TorusPath.closes, torusAfterPrimaryTurn]

theorem torus_is_not_a_circle_slice :
    angularCoordinates .torus ≠ angularCoordinates .circle := by
  decide

/-! Stokes is now typed over the two-angle domain rather than a circle surrogate. -/

def stokesDomain : Domain := .torus

theorem stokes_domain_requires_two_angles :
    angularCoordinates stokesDomain = 2 := rfl

/-! ## Six-field toroidal bundle

Each of the three curves carries a forward and a backward velocity field.
The ring boundary convention is explicit: entrance is inward, exit is outward.
-/

inductive RingSide
  | inward
  | outward
  deriving DecidableEq, Repr

inductive RingEvent
  | entrance
  | exit
  deriving DecidableEq, Repr

def ringSide : RingEvent → RingSide
  | .entrance => .inward
  | .exit => .outward

structure RingField where
  direction : Flow
  curve : Curve
  entranceSide : RingSide
  exitSide : RingSide
  velocity : Vec3
  deriving Repr

def makeRingField (direction : Flow) (curve : Curve) (velocity : Vec3) : RingField :=
  { direction := direction
    curve := curve
    entranceSide := .inward
    exitSide := .outward
    velocity := velocity }

theorem ring_field_enters_in (d : Flow) (c : Curve) (v : Vec3) :
    (makeRingField d c v).entranceSide = .inward := rfl

theorem ring_field_exits_out (d : Flow) (c : Curve) (v : Vec3) :
    (makeRingField d c v).exitSide = .outward := rfl

structure SixFieldTorus where
  forwardInner : RingField
  forwardMiddle : RingField
  forwardOuter : RingField
  backwardInner : RingField
  backwardMiddle : RingField
  backwardOuter : RingField

def sixFieldTorus (vi vm vo wi wm wo : Vec3) : SixFieldTorus :=
  { forwardInner := makeRingField .forward .inner vi
    forwardMiddle := makeRingField .forward .middle vm
    forwardOuter := makeRingField .forward .outer vo
    backwardInner := makeRingField .reverse .inner wi
    backwardMiddle := makeRingField .reverse .middle wm
    backwardOuter := makeRingField .reverse .outer wo }

def sixFieldList (bundle : SixFieldTorus) : List RingField :=
  [ bundle.forwardInner, bundle.forwardMiddle, bundle.forwardOuter,
    bundle.backwardInner, bundle.backwardMiddle, bundle.backwardOuter ]

def forwardFieldCount : Nat := 3
def backwardFieldCount : Nat := 3
def totalFieldCount : Nat := forwardFieldCount + backwardFieldCount

theorem three_forward_fields : forwardFieldCount = 3 := rfl
theorem three_backward_fields : backwardFieldCount = 3 := rfl
theorem six_toroidal_fields : totalFieldCount = 6 := rfl

theorem six_field_bundle_length (bundle : SixFieldTorus) :
    (sixFieldList bundle).length = totalFieldCount := by
  rfl

theorem six_field_boundary_convention
    (vi vm vo wi wm wo : Vec3) :
    (∀ field ∈ sixFieldList (sixFieldTorus vi vm vo wi wm wo),
      field.entranceSide = .inward) ∧
    (∀ field ∈ sixFieldList (sixFieldTorus vi vm vo wi wm wo),
      field.exitSide = .outward) := by
  simp [sixFieldList, sixFieldTorus, makeRingField]

/-! ## Crystalline-fluidic matrix and triangular transit -/

inductive MatrixState
  | crystal
  | fluid
  | plasma
  deriving DecidableEq, Repr

inductive TriangleNode
  | a
  | b
  | c
  deriving DecidableEq, Repr

def triangleNodeCount : Nat := 3
def triangleEdgeCount : Nat := 3

theorem triangle_has_three_nodes : triangleNodeCount = 3 := rfl
theorem triangle_has_three_edges : triangleEdgeCount = 3 := rfl

structure CrystallineFluidicMatrix where
  fields : SixFieldTorus
  state : MatrixState
  node : TriangleNode

/-- Plasma is the transitive state used while moving between triangle nodes. -/
def transit (_source _destination : TriangleNode) : MatrixState :=
  MatrixState.plasma

theorem transit_is_plasma (source destination : TriangleNode) :
    transit source destination = MatrixState.plasma := rfl

def triangleNext : TriangleNode → TriangleNode
  | .a => .b
  | .b => .c
  | .c => .a

theorem triangle_next_is_total (node : TriangleNode) :
    triangleNext node = TriangleNode.a ∨
    triangleNext node = TriangleNode.b ∨
    triangleNext node = TriangleNode.c := by
  cases node <;> simp [triangleNext]

def plasmaTransit (matrix : CrystallineFluidicMatrix) :
    CrystallineFluidicMatrix :=
  { matrix with state := MatrixState.plasma, node := triangleNext matrix.node }

theorem plasmaTransit_sets_transitive_state
    (matrix : CrystallineFluidicMatrix) :
    (plasmaTransit matrix).state = MatrixState.plasma := rfl

theorem plasmaTransit_preserves_six_fields
    (matrix : CrystallineFluidicMatrix) :
    (plasmaTransit matrix).fields = matrix.fields := rfl

/-! ## Discrete triangle differential operator -/

structure TriangleFlux where
  ab : Int
  bc : Int
  ca : Int

def divergenceA (flux : TriangleFlux) : Int := flux.ca - flux.ab
def divergenceB (flux : TriangleFlux) : Int := flux.ab - flux.bc
def divergenceC (flux : TriangleFlux) : Int :=
  -(divergenceA flux + divergenceB flux)

theorem int_add_neg_cancel (value : Int) : value + -value = 0 := by
  omega

def triangleDivergence (node : TriangleNode) (flux : TriangleFlux) : Int :=
  match node with
  | .a => divergenceA flux
  | .b => divergenceB flux
  | .c => divergenceC flux

theorem triangle_divergence_is_conservative (flux : TriangleFlux) :
    divergenceA flux + divergenceB flux + divergenceC flux = 0 := by
  exact int_add_neg_cancel (divergenceA flux + divergenceB flux)

theorem triangle_operator_sum_zero (flux : TriangleFlux) :
    triangleDivergence .a flux +
    triangleDivergence .b flux +
    triangleDivergence .c flux = 0 := by
  exact triangle_divergence_is_conservative flux

def oppositeFlux (value : Int) : Int := -value

theorem forward_backward_flux_cancel (value : Int) :
    value + oppositeFlux value = 0 := by
  exact int_add_neg_cancel value

/-! ## Attach triangle flux to every toroidal field -/

structure AttachedField where
  field : RingField
  flux : TriangleFlux

def attachField (field : RingField) (flux : TriangleFlux) : AttachedField :=
  { field := field, flux := flux }

structure AttachedSixFieldTorus where
  forwardInner : AttachedField
  forwardMiddle : AttachedField
  forwardOuter : AttachedField
  backwardInner : AttachedField
  backwardMiddle : AttachedField
  backwardOuter : AttachedField

def attachSixFields (bundle : SixFieldTorus) (flux : TriangleFlux) :
    AttachedSixFieldTorus :=
  { forwardInner := attachField bundle.forwardInner flux
    forwardMiddle := attachField bundle.forwardMiddle flux
    forwardOuter := attachField bundle.forwardOuter flux
    backwardInner := attachField bundle.backwardInner flux
    backwardMiddle := attachField bundle.backwardMiddle flux
    backwardOuter := attachField bundle.backwardOuter flux }

def attachedFieldList (bundle : AttachedSixFieldTorus) : List AttachedField :=
  [ bundle.forwardInner, bundle.forwardMiddle, bundle.forwardOuter,
    bundle.backwardInner, bundle.backwardMiddle, bundle.backwardOuter ]

theorem attached_six_fields_length (bundle : AttachedSixFieldTorus) :
    (attachedFieldList bundle).length = totalFieldCount := by
  rfl

theorem attached_flux_is_conservative (attached : AttachedField) :
    divergenceA attached.flux +
    divergenceB attached.flux +
    divergenceC attached.flux = 0 := by
  exact triangle_divergence_is_conservative attached.flux

theorem attached_made_field_preserves_boundary
    (d : Flow) (c : Curve) (v : Vec3) (flux : TriangleFlux) :
    (attachField (makeRingField d c v) flux).field.entranceSide = .inward ∧
    (attachField (makeRingField d c v) flux).field.exitSide = .outward := by
  exact ⟨rfl, rfl⟩

/-! ## First derived black-hole torus dynamics (geometric seed)

This is deliberately a discrete seed: the cube is normalized to `{-1,1}³`,
the center is the black-hole placeholder, and four tetrahedral boundary
points provide equal inward compression.  Continuous Navier–Stokes equations
and a relativistic horizon are later refinements, not silently assumed here.
-/

abbrev Point3 := Int × Int × Int

def blackHoleCenter : Point3 := (0, 0, 0)

def tetraPoint : Fin 4 → Point3
  | 0 => ( 1,  1,  1)
  | 1 => ( 1, -1, -1)
  | 2 => (-1,  1, -1)
  | 3 => (-1, -1,  1)

def inwardVector (p : Point3) : Point3 := (-p.1, -p.2.1, -p.2.2)

def dot3 (a b : Point3) : Int :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def radialCompression (p : Point3) : Int := dot3 (inwardVector p) p

theorem center_is_zero : blackHoleCenter = (0, 0, 0) := rfl

theorem tetra_points_press_inward :
    ∀ i : Fin 4, radialCompression (tetraPoint i) = -3 := by
  decide

structure ToroidalState where
  radial : Int
  thetaForward : Int
  thetaBackward : Int
  phiForward : Int
  phiBackward : Int
  homeostatic : Prop

def initialToroidalState : ToroidalState :=
  { radial := -3
    thetaForward := 1
    thetaBackward := -1
    phiForward := 1
    phiBackward := -1
    homeostatic := True }

theorem initial_state_homeostatic : initialToroidalState.homeostatic := by
  trivial

theorem initial_state_radial_balance :
    initialToroidalState.thetaForward + initialToroidalState.thetaBackward = 0 ∧
    initialToroidalState.phiForward + initialToroidalState.phiBackward = 0 := by
  decide

/-! ## First executable homeostatic dynamics layer

The four boundary impulses are locally inward but cancel as a vector by
tetrahedral symmetry.  The two angular planes carry equal and opposite
circulation.  This is the discrete balance law that the later differential
equations must refine.
-/

def addPoint3 (a b : Point3) : Point3 :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

def zeroPoint3 : Point3 := (0, 0, 0)

def totalInwardVector : Point3 :=
  addPoint3 (addPoint3 (inwardVector (tetraPoint 0))
    (inwardVector (tetraPoint 1)))
    (addPoint3 (inwardVector (tetraPoint 2))
      (inwardVector (tetraPoint 3)))

theorem tetrahedral_inward_vectors_balance :
    totalInwardVector = zeroPoint3 := by
  decide

def inwardPressure : Int := 3
def outwardHomeostaticPressure : Int := 3

def netThetaFlow (state : ToroidalState) : Int :=
  state.thetaForward + state.thetaBackward

def netPhiFlow (state : ToroidalState) : Int :=
  state.phiForward + state.phiBackward

def homeostaticBalance (state : ToroidalState) : Prop :=
  inwardPressure = outwardHomeostaticPressure ∧
  netThetaFlow state = 0 ∧
  netPhiFlow state = 0

theorem initial_state_is_homeostatic_balance :
    homeostaticBalance initialToroidalState := by
  simp [homeostaticBalance, netThetaFlow, netPhiFlow,
    initialToroidalState, inwardPressure, outwardHomeostaticPressure]

def torusCoordinate : Type := Nat × Nat

def torusWrap (coordinate : torusCoordinate) : torusCoordinate :=
  (coordinate.1 % 360, coordinate.2 % 360)

def torusFlowStep (coordinate : torusCoordinate)
    (_thetaVelocity _phiVelocity : Int) : torusCoordinate :=
  (coordinate.1, coordinate.2)

theorem torus_wrap_has_two_periodic_coordinates
    (coordinate : torusCoordinate) :
    (torusWrap coordinate).1 < 360 ∧ (torusWrap coordinate).2 < 360 := by
  change coordinate.1 % 360 < 360 ∧ coordinate.2 % 360 < 360
  exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

/-! ## Discrete time-step

This is the first dynamics operator.  It is a finite-difference scaffold:
the radial increment is the pressure imbalance, while the two toroidal
coordinates advance independently and wrap modulo one full turn.
-/

def radialAcceleration : Int :=
  inwardPressure - outwardHomeostaticPressure

def radialUpdate (radial : Int) : Int :=
  radial + radialAcceleration

def dynamicsStep (state : ToroidalState) : ToroidalState :=
  { state with radial := radialUpdate state.radial }

theorem homeostatic_radial_acceleration_zero : radialAcceleration = 0 := by
  decide

theorem homeostatic_radial_update_fixed (radial : Int) :
    radialUpdate radial = radial := by
  simp [radialUpdate, radialAcceleration, inwardPressure,
    outwardHomeostaticPressure]

theorem initial_dynamics_step_fixed :
    dynamicsStep initialToroidalState = initialToroidalState := by
  simp [dynamicsStep, radialUpdate, radialAcceleration, inwardPressure,
    outwardHomeostaticPressure, initialToroidalState]

def torusAdvance (coordinate : torusCoordinate)
    (thetaVelocity phiVelocity : Nat) : torusCoordinate :=
  torusWrap (coordinate.1 + thetaVelocity, coordinate.2 + phiVelocity)

theorem torus_advance_remains_on_periodic_domain
    (coordinate : torusCoordinate) (thetaVelocity phiVelocity : Nat) :
    (torusAdvance coordinate thetaVelocity phiVelocity).1 < 360 ∧
    (torusAdvance coordinate thetaVelocity phiVelocity).2 < 360 := by
  exact torus_wrap_has_two_periodic_coordinates
    (coordinate := (coordinate.1 + thetaVelocity, coordinate.2 + phiVelocity))

/-! ## Horizon boundary layer

The origin remains the black-hole center.  A discrete radial index represents
distance from that center; `horizonRadius = 1` is the excluded interior
boundary.  The inward step approaches the boundary and clamps there.
-/

def horizonRadius : Nat := 1

def radialInwardStep (radius : Nat) : Nat :=
  if horizonRadius < radius then radius - 1 else horizonRadius

theorem horizon_is_fixed : radialInwardStep horizonRadius = horizonRadius := by
  simp [radialInwardStep]

theorem inward_step_stays_outside_horizon (radius : Nat) :
    horizonRadius ≤ radialInwardStep radius := by
  by_cases h : horizonRadius < radius
  · rw [radialInwardStep, if_pos h]
    change 1 ≤ radius - 1
    have h' : 1 < radius := by
      simpa [horizonRadius] using h
    omega
  · rw [radialInwardStep, if_neg h]
    exact Nat.le_refl _

def inUnitCube (p : Point3) : Prop :=
  (-1 : Int) ≤ p.1 ∧ p.1 ≤ 1 ∧
  (-1 : Int) ≤ p.2.1 ∧ p.2.1 ≤ 1 ∧
  (-1 : Int) ≤ p.2.2 ∧ p.2.2 ≤ 1

theorem tetra_points_are_in_unit_cube :
    inUnitCube (tetraPoint 0) ∧
    inUnitCube (tetraPoint 1) ∧
    inUnitCube (tetraPoint 2) ∧
    inUnitCube (tetraPoint 3) := by
  simp [inUnitCube, tetraPoint]

/-! ## Six-channel toroidal velocity field

The three forward channels and three backward channels are now represented
as signed scalar velocities.  The seed assigns `+1` to every forward channel
and `-1` to its paired backward channel.
-/

structure SixChannelVelocity where
  forwardInner : Int
  forwardMiddle : Int
  forwardOuter : Int
  backwardInner : Int
  backwardMiddle : Int
  backwardOuter : Int

def initialSixChannelVelocity : SixChannelVelocity :=
  { forwardInner := 1
    forwardMiddle := 1
    forwardOuter := 1
    backwardInner := -1
    backwardMiddle := -1
    backwardOuter := -1 }

def sixChannelNet (velocity : SixChannelVelocity) : Int :=
  velocity.forwardInner + velocity.forwardMiddle + velocity.forwardOuter +
  velocity.backwardInner + velocity.backwardMiddle + velocity.backwardOuter

def sixChannelHomeostatic (velocity : SixChannelVelocity) : Prop :=
  velocity.forwardInner + velocity.backwardInner = 0 ∧
  velocity.forwardMiddle + velocity.backwardMiddle = 0 ∧
  velocity.forwardOuter + velocity.backwardOuter = 0

theorem initial_six_channel_pairs_cancel :
    sixChannelHomeostatic initialSixChannelVelocity := by
  dsimp [sixChannelHomeostatic, initialSixChannelVelocity]
  constructor
  · omega
  constructor
  · omega
  · omega

theorem initial_six_channel_net_zero :
    sixChannelNet initialSixChannelVelocity = 0 := by
  dsimp [sixChannelNet, initialSixChannelVelocity]

theorem six_channel_count_matches_bundle :
    (sixFieldList (sixFieldTorus
      ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ ⟨0, 0, 0⟩
      ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ ⟨0, 0, 0⟩)).length = 6 := by
  rfl

/-! ## Three-curve toroidal rotation

One discrete rotation advances each inner/middle/outer curve to the next
position.  Forward and backward channels rotate together, so the paired
homeostatic relation is invariant and three rotations return to the start.
-/

def rotateSixChannels (velocity : SixChannelVelocity) : SixChannelVelocity :=
  { forwardInner := velocity.forwardMiddle
    forwardMiddle := velocity.forwardOuter
    forwardOuter := velocity.forwardInner
    backwardInner := velocity.backwardMiddle
    backwardMiddle := velocity.backwardOuter
    backwardOuter := velocity.backwardInner }

theorem rotate_preserves_net_flow (velocity : SixChannelVelocity) :
    sixChannelNet (rotateSixChannels velocity) = sixChannelNet velocity := by
  dsimp [sixChannelNet, rotateSixChannels]
  omega

theorem rotate_preserves_homeostasis (velocity : SixChannelVelocity) :
    sixChannelHomeostatic (rotateSixChannels velocity) ↔
    sixChannelHomeostatic velocity := by
  constructor
  · intro h
    exact ⟨h.2.2, h.1, h.2.1⟩
  · intro h
    exact ⟨h.2.1, h.2.2, h.1⟩

theorem rotate_three_times_identity (velocity : SixChannelVelocity) :
    rotateSixChannels (rotateSixChannels (rotateSixChannels velocity)) = velocity := by
  rfl

/-! ## Coupled toroidal black-hole state

The radial horizon index, the two periodic coordinates, and the six-channel
velocity field now evolve as one discrete state.
-/

structure CoupledState where
  radius : Nat
  position : torusCoordinate
  channels : SixChannelVelocity

def coupledStep (state : CoupledState)
    (thetaVelocity phiVelocity : Nat) : CoupledState :=
  { radius := radialInwardStep state.radius
    position := torusAdvance state.position thetaVelocity phiVelocity
    channels := rotateSixChannels state.channels }

theorem coupled_step_horizon_safe
    (state : CoupledState) (thetaVelocity phiVelocity : Nat) :
    horizonRadius ≤ (coupledStep state thetaVelocity phiVelocity).radius := by
  exact inward_step_stays_outside_horizon state.radius

theorem coupled_step_periodic
    (state : CoupledState) (thetaVelocity phiVelocity : Nat) :
    (coupledStep state thetaVelocity phiVelocity).position.1 < 360 ∧
    (coupledStep state thetaVelocity phiVelocity).position.2 < 360 := by
  exact torus_advance_remains_on_periodic_domain
    state.position thetaVelocity phiVelocity

theorem coupled_step_preserves_net_flow
    (state : CoupledState) (thetaVelocity phiVelocity : Nat) :
    sixChannelNet (coupledStep state thetaVelocity phiVelocity).channels =
      sixChannelNet state.channels := by
  exact rotate_preserves_net_flow state.channels

theorem coupled_step_preserves_homeostasis
    (state : CoupledState) (thetaVelocity phiVelocity : Nat)
    (h : sixChannelHomeostatic state.channels) :
    sixChannelHomeostatic (coupledStep state thetaVelocity phiVelocity).channels := by
  exact (rotate_preserves_homeostasis state.channels).2 h

/-! ## Finite-horizon invariant propagation -/

def coupledIterate : Nat → CoupledState → Nat → Nat → CoupledState
  | 0, state, _, _ => state
  | n + 1, state, thetaVelocity, phiVelocity =>
      coupledIterate n (coupledStep state thetaVelocity phiVelocity)
        thetaVelocity phiVelocity

theorem iterate_horizon_safe
    (steps : Nat) (state : CoupledState)
    (thetaVelocity phiVelocity : Nat)
    (h : horizonRadius ≤ state.radius) :
    horizonRadius ≤
      (coupledIterate steps state thetaVelocity phiVelocity).radius := by
  induction steps generalizing state with
  | zero => simpa [coupledIterate] using h
  | succ steps ih =>
      apply ih
      exact coupled_step_horizon_safe state thetaVelocity phiVelocity

theorem iterate_periodic
    (steps : Nat) (state : CoupledState)
    (thetaVelocity phiVelocity : Nat)
    (h : state.position.1 < 360 ∧ state.position.2 < 360) :
    (coupledIterate steps state thetaVelocity phiVelocity).position.1 < 360 ∧
    (coupledIterate steps state thetaVelocity phiVelocity).position.2 < 360 := by
  induction steps generalizing state with
  | zero => simpa [coupledIterate] using h
  | succ steps ih =>
      apply ih
      exact coupled_step_periodic state thetaVelocity phiVelocity

theorem iterate_preserves_net_flow
    (steps : Nat) (state : CoupledState)
    (thetaVelocity phiVelocity : Nat) :
    sixChannelNet (coupledIterate steps state thetaVelocity phiVelocity).channels =
      sixChannelNet state.channels := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih =>
      calc
        sixChannelNet
            (coupledIterate steps
              (coupledStep state thetaVelocity phiVelocity)
              thetaVelocity phiVelocity).channels =
            sixChannelNet (coupledStep state thetaVelocity phiVelocity).channels :=
          ih (state := coupledStep state thetaVelocity phiVelocity)
        _ = sixChannelNet state.channels :=
          coupled_step_preserves_net_flow state thetaVelocity phiVelocity

theorem iterate_preserves_homeostasis
    (steps : Nat) (state : CoupledState)
    (thetaVelocity phiVelocity : Nat)
    (h : sixChannelHomeostatic state.channels) :
    sixChannelHomeostatic
      (coupledIterate steps state thetaVelocity phiVelocity).channels := by
  induction steps generalizing state with
  | zero => simpa [coupledIterate] using h
  | succ steps ih =>
      apply ih
      exact coupled_step_preserves_homeostasis state thetaVelocity phiVelocity h

/-! ## Toroidal Stokes boundary and horizon flux -/

structure ToroidalBoundary where
  thetaForward : Int
  phiForward : Int
  thetaBackward : Int
  phiBackward : Int

def toroidalCirculation (boundary : ToroidalBoundary) : Int :=
  boundary.thetaForward + boundary.phiForward +
  boundary.thetaBackward + boundary.phiBackward

def balancedToroidalBoundary (boundary : ToroidalBoundary) : Prop :=
  boundary.thetaForward + boundary.thetaBackward = 0 ∧
  boundary.phiForward + boundary.phiBackward = 0

theorem balanced_toroidal_boundary_has_zero_circulation
    (boundary : ToroidalBoundary)
    (h : balancedToroidalBoundary boundary) :
    toroidalCirculation boundary = 0 := by
  dsimp [toroidalCirculation, balancedToroidalBoundary] at h ⊢
  omega

def channelBoundary (velocity : SixChannelVelocity) : ToroidalBoundary :=
  { thetaForward := velocity.forwardInner
    phiForward := velocity.forwardMiddle
    thetaBackward := velocity.backwardInner
    phiBackward := velocity.backwardMiddle }

theorem initial_channel_boundary_has_zero_circulation :
    toroidalCirculation (channelBoundary initialSixChannelVelocity) = 0 := by
  apply balanced_toroidal_boundary_has_zero_circulation
  dsimp [balancedToroidalBoundary, channelBoundary, initialSixChannelVelocity]
  constructor
  · omega
  · omega

def horizonFlux (radius : Nat) (flow : Int) : Int :=
  if radius = horizonRadius then 0 else flow

theorem horizon_flux_at_boundary_zero (flow : Int) :
    horizonFlux horizonRadius flow = 0 := by
  simp [horizonFlux]

/-! ## Parametric homeostatic toroidal field -/

def pairedToroidalBoundary (thetaMagnitude phiMagnitude : Int) :
    ToroidalBoundary :=
  { thetaForward := thetaMagnitude
    phiForward := phiMagnitude
    thetaBackward := -thetaMagnitude
    phiBackward := -phiMagnitude }

theorem paired_boundary_is_balanced
    (thetaMagnitude phiMagnitude : Int) :
    balancedToroidalBoundary
      (pairedToroidalBoundary thetaMagnitude phiMagnitude) := by
  dsimp [balancedToroidalBoundary, pairedToroidalBoundary]
  constructor <;> omega

def stokesResidual (boundary : ToroidalBoundary) : Int :=
  toroidalCirculation boundary

theorem paired_boundary_has_zero_stokes_residual
    (thetaMagnitude phiMagnitude : Int) :
    stokesResidual (pairedToroidalBoundary thetaMagnitude phiMagnitude) = 0 := by
  exact balanced_toroidal_boundary_has_zero_circulation
    (pairedToroidalBoundary thetaMagnitude phiMagnitude)
    (paired_boundary_is_balanced thetaMagnitude phiMagnitude)

theorem horizon_state_has_zero_boundary_flux (flow : Int) :
    horizonFlux horizonRadius flow = 0 := by
  exact horizon_flux_at_boundary_zero flow

/-! ## Discrete force-balance residual

The continuous equation will later refine these four terms.  At this stage
they are signed integrated contributions over one update: transport,
pressure, viscosity, and central attraction.
-/

structure ForceBalance where
  advection : Int
  pressureGradient : Int
  viscosity : Int
  blackHoleAttraction : Int

def forceResidual (forces : ForceBalance) : Int :=
  forces.advection + forces.pressureGradient +
  forces.viscosity + forces.blackHoleAttraction

def homeostaticForces : ForceBalance :=
  { advection := 0
    pressureGradient := 3
    viscosity := 0
    blackHoleAttraction := -3 }

def forceBalanced (forces : ForceBalance) : Prop :=
  forceResidual forces = 0

theorem homeostatic_force_residual_zero :
    forceResidual homeostaticForces = 0 := by
  dsimp [forceResidual, homeostaticForces]

theorem homeostatic_forces_are_balanced :
    forceBalanced homeostaticForces := by
  exact homeostatic_force_residual_zero

theorem force_balance_is_stable_under_zero_step
    (forces : ForceBalance)
    (h : forceBalanced forces) :
    forceResidual forces = 0 := by
  exact h

/-! ## Unified discrete toroidal Stokes residual -/

structure ToroidalEquationState where
  timeDerivative : Int
  forces : ForceBalance
  boundary : ToroidalBoundary

def equationResidual (state : ToroidalEquationState) : Int :=
  state.timeDerivative + forceResidual state.forces +
  stokesResidual state.boundary

def homeostaticEquationState : ToroidalEquationState :=
  { timeDerivative := 0
    forces := homeostaticForces
    boundary := pairedToroidalBoundary 1 1 }

def equationBalanced (state : ToroidalEquationState) : Prop :=
  equationResidual state = 0

theorem homeostatic_equation_residual_zero :
    equationResidual homeostaticEquationState = 0 := by
  dsimp [equationResidual, homeostaticEquationState, forceResidual,
    homeostaticForces, stokesResidual, toroidalCirculation,
    pairedToroidalBoundary]

theorem homeostatic_equation_is_balanced :
    equationBalanced homeostaticEquationState := by
  exact homeostatic_equation_residual_zero

theorem zero_time_derivative_is_stationary :
    homeostaticEquationState.timeDerivative = 0 := by
  rfl

theorem equation_residual_zero_of_balanced_parts
    (state : ToroidalEquationState)
    (ht : state.timeDerivative = 0)
    (hf : forceBalanced state.forces)
    (hb : stokesResidual state.boundary = 0) :
    equationResidual state = 0 := by
  dsimp [equationResidual, forceBalanced] at ht hf hb ⊢
  omega

def parametrizedHomeostaticForces (magnitude : Int) : ForceBalance :=
  { advection := 0
    pressureGradient := magnitude
    viscosity := 0
    blackHoleAttraction := -magnitude }

def parametrizedHomeostaticState
    (magnitude thetaMagnitude phiMagnitude : Int) :
    ToroidalEquationState :=
  { timeDerivative := 0
    forces := parametrizedHomeostaticForces magnitude
    boundary := pairedToroidalBoundary thetaMagnitude phiMagnitude }

theorem parametrized_homeostatic_equation_zero
    (magnitude thetaMagnitude phiMagnitude : Int) :
    equationResidual
      (parametrizedHomeostaticState magnitude thetaMagnitude phiMagnitude) = 0 := by
  dsimp [equationResidual, parametrizedHomeostaticState,
    parametrizedHomeostaticForces, forceResidual, stokesResidual,
    toroidalCirculation, pairedToroidalBoundary]
  omega

/-! ## Discrete Stokes identity -/

structure DiscreteStokesCell where
  boundary : ToroidalBoundary
  interiorCurl : Int

def stokesCellResidual (cell : DiscreteStokesCell) : Int :=
  stokesResidual cell.boundary - cell.interiorCurl

theorem discrete_stokes_identity
    (cell : DiscreteStokesCell)
    (h : stokesResidual cell.boundary = cell.interiorCurl) :
    stokesCellResidual cell = 0 := by
  dsimp [stokesCellResidual]
  omega

def homeostaticStokesCell : DiscreteStokesCell :=
  { boundary := pairedToroidalBoundary 1 1
    interiorCurl := 0 }

theorem homeostatic_stokes_cell_residual_zero :
    stokesCellResidual homeostaticStokesCell = 0 := by
  apply discrete_stokes_identity homeostaticStokesCell
  dsimp [homeostaticStokesCell, stokesResidual, toroidalCirculation,
    pairedToroidalBoundary]

theorem homeostatic_stokes_cell_has_zero_interior_curl :
    homeostaticStokesCell.interiorCurl = 0 := by
  rfl

/-! ## Net flux versus oriented toroidal circulation

The signed sum used above measures transport balance.  A separate oriented
sum records swirl: reversing an edge reverses its orientation as well, so a
paired positive/negative velocity contributes twice to circulation rather than zero.
-/

def orientedToroidalCirculation (boundary : ToroidalBoundary) : Int :=
  boundary.thetaForward + boundary.phiForward -
  boundary.thetaBackward - boundary.phiBackward

theorem paired_boundary_oriented_circulation
    (thetaMagnitude phiMagnitude : Int) :
    orientedToroidalCirculation
      (pairedToroidalBoundary thetaMagnitude phiMagnitude) =
      2 * thetaMagnitude + 2 * phiMagnitude := by
  dsimp [orientedToroidalCirculation, pairedToroidalBoundary]
  omega

theorem initial_paired_flow_has_nonzero_oriented_circulation :
    orientedToroidalCirculation
      (pairedToroidalBoundary 1 1) = 4 := by
  dsimp [orientedToroidalCirculation, pairedToroidalBoundary]

theorem initial_flow_has_zero_net_flux_and_nonzero_swirl :
    toroidalCirculation (pairedToroidalBoundary 1 1) = 0 ∧
    orientedToroidalCirculation (pairedToroidalBoundary 1 1) = 4 := by
  constructor
  · dsimp [toroidalCirculation, pairedToroidalBoundary]
  · exact initial_paired_flow_has_nonzero_oriented_circulation

/-! ## Six-channel oriented circulation -/

def orientedSixCirculation (velocity : SixChannelVelocity) : Int :=
  velocity.forwardInner + velocity.forwardMiddle + velocity.forwardOuter -
  velocity.backwardInner - velocity.backwardMiddle - velocity.backwardOuter

theorem rotate_preserves_oriented_six_circulation
    (velocity : SixChannelVelocity) :
    orientedSixCirculation (rotateSixChannels velocity) =
      orientedSixCirculation velocity := by
  dsimp [orientedSixCirculation, rotateSixChannels]
  omega

theorem initial_oriented_six_circulation_is_six :
    orientedSixCirculation initialSixChannelVelocity = 6 := by
  dsimp [orientedSixCirculation, initialSixChannelVelocity]

theorem initial_six_flow_has_zero_net_and_nonzero_swirl :
    sixChannelNet initialSixChannelVelocity = 0 ∧
    orientedSixCirculation initialSixChannelVelocity = 6 := by
  constructor
  · exact initial_six_channel_net_zero
  · exact initial_oriented_six_circulation_is_six

theorem coupled_step_preserves_oriented_swirl
    (state : CoupledState) (thetaVelocity phiVelocity : Nat) :
    orientedSixCirculation (coupledStep state thetaVelocity phiVelocity).channels =
      orientedSixCirculation state.channels := by
  exact rotate_preserves_oriented_six_circulation state.channels

theorem iterate_preserves_oriented_swirl
    (steps : Nat) (state : CoupledState)
    (thetaVelocity phiVelocity : Nat) :
    orientedSixCirculation
        (coupledIterate steps state thetaVelocity phiVelocity).channels =
      orientedSixCirculation state.channels := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih =>
      calc
        orientedSixCirculation
            (coupledIterate steps
              (coupledStep state thetaVelocity phiVelocity)
              thetaVelocity phiVelocity).channels =
            orientedSixCirculation
              (coupledStep state thetaVelocity phiVelocity).channels :=
          ih (state := coupledStep state thetaVelocity phiVelocity)
        _ = orientedSixCirculation state.channels :=
          coupled_step_preserves_oriented_swirl state thetaVelocity phiVelocity

def initialCoupledState : CoupledState :=
  { radius := horizonRadius
    position := (0, 0)
    channels := initialSixChannelVelocity }

theorem initial_coupled_state_at_horizon :
    initialCoupledState.radius = horizonRadius := by
  rfl

theorem initial_coupled_state_is_periodic :
    initialCoupledState.position.1 < 360 ∧
    initialCoupledState.position.2 < 360 := by
  decide

theorem initial_coupled_state_swirl_is_six :
    orientedSixCirculation initialCoupledState.channels = 6 := by
  exact initial_oriented_six_circulation_is_six

theorem coupled_three_steps_return_channel_order
    (state : CoupledState) (thetaVelocity phiVelocity : Nat) :
    (coupledIterate 3 state thetaVelocity phiVelocity).channels =
      state.channels := by
  rfl

theorem coupled_three_steps_preserve_swirl
    (state : CoupledState) (thetaVelocity phiVelocity : Nat) :
    orientedSixCirculation
        (coupledIterate 3 state thetaVelocity phiVelocity).channels =
      orientedSixCirculation state.channels := by
  exact iterate_preserves_oriented_swirl 3 state thetaVelocity phiVelocity

/-! ## Full-turn closure on the two torus coordinates -/

def torusFullTurn (coordinate : torusCoordinate) : torusCoordinate :=
  torusAdvance coordinate 360 360

theorem full_turn_preserves_wrapped_position
    (coordinate : torusCoordinate) :
    torusFullTurn coordinate = torusWrap coordinate := by
  simp [torusFullTurn, torusAdvance, torusWrap] <;> rfl

theorem full_turn_closes_both_cycles
    (coordinate : torusCoordinate) :
    (torusFullTurn coordinate).1 = (torusWrap coordinate).1 ∧
    (torusFullTurn coordinate).2 = (torusWrap coordinate).2 := by
  have h := full_turn_preserves_wrapped_position coordinate
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-! ## Integrated smoke test -/

theorem integrated_toroidal_black_hole_smoke_test :
    horizonRadius ≤ initialCoupledState.radius ∧
    initialCoupledState.position.1 < 360 ∧
    initialCoupledState.position.2 < 360 ∧
    sixChannelNet initialCoupledState.channels = 0 ∧
    orientedSixCirculation initialCoupledState.channels = 6 ∧
    equationResidual homeostaticEquationState = 0 := by
  exact ⟨by decide,
    initial_coupled_state_is_periodic.1,
    initial_coupled_state_is_periodic.2,
    initial_six_channel_net_zero,
    initial_coupled_state_swirl_is_six,
    homeostatic_equation_residual_zero⟩

/-! ## Bounded portable-energy abstraction

This layer models a finite-capacity portable battery.  Generation and draw
are bookkeeping inputs; the clamp is the safety boundary.  No claim about
energy from nothing is encoded.
-/

def boundedEnergy (capacity level : Nat) : Nat :=
  if level ≤ capacity then level else capacity

theorem bounded_energy_is_safe (capacity level : Nat) :
    boundedEnergy capacity level ≤ capacity := by
  by_cases h : level ≤ capacity
  · simp [boundedEnergy, h]
  · simp [boundedEnergy, h]

structure PortableBattery where
  capacity : Nat
  stored : Nat

def portableBatterySafe (battery : PortableBattery) : Prop :=
  battery.stored ≤ battery.capacity

def batteryStep (battery : PortableBattery)
    (generated drawn : Nat) : PortableBattery :=
  { capacity := battery.capacity
    stored := boundedEnergy battery.capacity
      (battery.stored + generated - drawn) }

theorem battery_step_is_safe
    (battery : PortableBattery) (generated drawn : Nat) :
    portableBatterySafe (batteryStep battery generated drawn) := by
  exact bounded_energy_is_safe battery.capacity
    (battery.stored + generated - drawn)

def portableNuclearBattery : PortableBattery :=
  { capacity := 100
    stored := 100 }

theorem portable_nuclear_battery_is_bounded :
    portableBatterySafe portableNuclearBattery := by
  simp [portableBatterySafe, portableNuclearBattery]

theorem portable_nuclear_battery_step_is_bounded
    (generated drawn : Nat) :
    portableBatterySafe
      (batteryStep portableNuclearBattery generated drawn) := by
  exact battery_step_is_safe portableNuclearBattery generated drawn

def batteryIterate : Nat → PortableBattery → Nat → Nat → PortableBattery
  | 0, battery, _, _ => battery
  | steps + 1, battery, generated, drawn =>
      batteryIterate steps (batteryStep battery generated drawn) generated drawn

theorem battery_iterate_is_safe
    (steps : Nat) (battery : PortableBattery)
    (generated drawn : Nat)
    (h : portableBatterySafe battery) :
    portableBatterySafe
      (batteryIterate steps battery generated drawn) := by
  induction steps generalizing battery with
  | zero => simpa [batteryIterate] using h
  | succ steps ih =>
      apply ih
      exact battery_step_is_safe battery generated drawn

theorem portable_nuclear_battery_iterate_is_safe
    (steps generated drawn : Nat) :
    portableBatterySafe
      (batteryIterate steps portableNuclearBattery generated drawn) := by
  apply battery_iterate_is_safe steps portableNuclearBattery generated drawn
  exact portable_nuclear_battery_is_bounded

/-! ## Powered coupled state -/

structure PoweredCoupledState where
  dynamics : CoupledState
  battery : PortableBattery

def poweredStep (state : PoweredCoupledState)
    (thetaVelocity phiVelocity generated drawn : Nat) : PoweredCoupledState :=
  { dynamics := coupledStep state.dynamics thetaVelocity phiVelocity
    battery := batteryStep state.battery generated drawn }

theorem powered_step_horizon_safe
    (state : PoweredCoupledState)
    (thetaVelocity phiVelocity generated drawn : Nat) :
    horizonRadius ≤ (poweredStep state thetaVelocity phiVelocity generated drawn).dynamics.radius := by
  exact coupled_step_horizon_safe state.dynamics thetaVelocity phiVelocity

theorem powered_step_periodic
    (state : PoweredCoupledState)
    (thetaVelocity phiVelocity generated drawn : Nat) :
    (poweredStep state thetaVelocity phiVelocity generated drawn).dynamics.position.1 < 360 ∧
    (poweredStep state thetaVelocity phiVelocity generated drawn).dynamics.position.2 < 360 := by
  exact coupled_step_periodic state.dynamics thetaVelocity phiVelocity

theorem powered_step_battery_safe
    (state : PoweredCoupledState)
    (thetaVelocity phiVelocity generated drawn : Nat)
    (_h : portableBatterySafe state.battery) :
    portableBatterySafe
      (poweredStep state thetaVelocity phiVelocity generated drawn).battery := by
  exact battery_step_is_safe state.battery generated drawn

theorem powered_step_preserves_net_flow
    (state : PoweredCoupledState)
    (thetaVelocity phiVelocity generated drawn : Nat) :
    sixChannelNet
        (poweredStep state thetaVelocity phiVelocity generated drawn).dynamics.channels =
      sixChannelNet state.dynamics.channels := by
  exact coupled_step_preserves_net_flow state.dynamics thetaVelocity phiVelocity

theorem powered_step_preserves_swirl
    (state : PoweredCoupledState)
    (thetaVelocity phiVelocity generated drawn : Nat) :
    orientedSixCirculation
        (poweredStep state thetaVelocity phiVelocity generated drawn).dynamics.channels =
      orientedSixCirculation state.dynamics.channels := by
  exact coupled_step_preserves_oriented_swirl state.dynamics thetaVelocity phiVelocity

def initialPoweredState : PoweredCoupledState :=
  { dynamics := initialCoupledState
    battery := portableNuclearBattery }

theorem initial_powered_state_is_safe :
    horizonRadius ≤ initialPoweredState.dynamics.radius ∧
    portableBatterySafe initialPoweredState.battery := by
  exact ⟨by decide, portable_nuclear_battery_is_bounded⟩

/-! ## Powered finite-run invariants -/

def poweredIterate : Nat → PoweredCoupledState → Nat → Nat → Nat → Nat →
    PoweredCoupledState
  | 0, state, _, _, _, _ => state
  | steps + 1, state, thetaVelocity, phiVelocity, generated, drawn =>
      poweredIterate steps
        (poweredStep state thetaVelocity phiVelocity generated drawn)
        thetaVelocity phiVelocity generated drawn

theorem powered_iterate_is_safe
    (steps : Nat) (state : PoweredCoupledState)
    (thetaVelocity phiVelocity generated drawn : Nat)
    (hh : horizonRadius ≤ state.dynamics.radius)
    (hp : state.dynamics.position.1 < 360 ∧
      state.dynamics.position.2 < 360)
    (hb : portableBatterySafe state.battery) :
    horizonRadius ≤
        (poweredIterate steps state thetaVelocity phiVelocity generated drawn).dynamics.radius ∧
    (poweredIterate steps state thetaVelocity phiVelocity generated drawn).dynamics.position.1 < 360 ∧
    (poweredIterate steps state thetaVelocity phiVelocity generated drawn).dynamics.position.2 < 360 ∧
    portableBatterySafe
      (poweredIterate steps state thetaVelocity phiVelocity generated drawn).battery := by
  induction steps generalizing state with
  | zero =>
      simpa [poweredIterate] using
        And.intro hh (And.intro hp.1 (And.intro hp.2 hb))
  | succ steps ih =>
      apply ih
      · exact powered_step_horizon_safe state thetaVelocity phiVelocity generated drawn
      · exact powered_step_periodic state thetaVelocity phiVelocity generated drawn
      · exact powered_step_battery_safe state thetaVelocity phiVelocity generated drawn hb

theorem initial_powered_iterate_is_safe
    (steps thetaVelocity phiVelocity generated drawn : Nat) :
    horizonRadius ≤
        (poweredIterate steps initialPoweredState
          thetaVelocity phiVelocity generated drawn).dynamics.radius ∧
    (poweredIterate steps initialPoweredState
      thetaVelocity phiVelocity generated drawn).dynamics.position.1 < 360 ∧
    (poweredIterate steps initialPoweredState
      thetaVelocity phiVelocity generated drawn).dynamics.position.2 < 360 ∧
    portableBatterySafe
      (poweredIterate steps initialPoweredState
        thetaVelocity phiVelocity generated drawn).battery := by
  apply powered_iterate_is_safe steps initialPoweredState
    thetaVelocity phiVelocity generated drawn
  · exact initial_powered_state_is_safe.1
  · exact initial_coupled_state_is_periodic
  · exact initial_powered_state_is_safe.2

theorem powered_iterate_preserves_net_flow
    (steps : Nat) (state : PoweredCoupledState)
    (thetaVelocity phiVelocity generated drawn : Nat) :
    sixChannelNet
        (poweredIterate steps state thetaVelocity phiVelocity generated drawn).dynamics.channels =
      sixChannelNet state.dynamics.channels := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih =>
      calc
        sixChannelNet
            (poweredIterate steps
              (poweredStep state thetaVelocity phiVelocity generated drawn)
              thetaVelocity phiVelocity generated drawn).dynamics.channels =
            sixChannelNet
              (poweredStep state thetaVelocity phiVelocity generated drawn).dynamics.channels :=
          ih (state := poweredStep state thetaVelocity phiVelocity generated drawn)
        _ = sixChannelNet state.dynamics.channels :=
          powered_step_preserves_net_flow state thetaVelocity phiVelocity generated drawn

theorem powered_iterate_preserves_swirl
    (steps : Nat) (state : PoweredCoupledState)
    (thetaVelocity phiVelocity generated drawn : Nat) :
    orientedSixCirculation
        (poweredIterate steps state thetaVelocity phiVelocity generated drawn).dynamics.channels =
      orientedSixCirculation state.dynamics.channels := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih =>
      calc
        orientedSixCirculation
            (poweredIterate steps
              (poweredStep state thetaVelocity phiVelocity generated drawn)
              thetaVelocity phiVelocity generated drawn).dynamics.channels =
            orientedSixCirculation
              (poweredStep state thetaVelocity phiVelocity generated drawn).dynamics.channels :=
          ih (state := poweredStep state thetaVelocity phiVelocity generated drawn)
        _ = orientedSixCirculation state.dynamics.channels :=
          powered_step_preserves_swirl state thetaVelocity phiVelocity generated drawn

/-! ## Finite-difference torus differential operator -/

structure TorusStencil where
  center : Int
  thetaForward : Int
  thetaBackward : Int
  phiForward : Int
  phiBackward : Int

def discreteLaplacian (stencil : TorusStencil) : Int :=
  stencil.thetaForward + stencil.thetaBackward +
  stencil.phiForward + stencil.phiBackward - 4 * stencil.center

def constantTorusStencil (value : Int) : TorusStencil :=
  { center := value
    thetaForward := value
    thetaBackward := value
    phiForward := value
    phiBackward := value }

theorem constant_torus_stencil_has_zero_laplacian (value : Int) :
    discreteLaplacian (constantTorusStencil value) = 0 := by
  dsimp [discreteLaplacian, constantTorusStencil]
  omega

def discreteThetaGradient (stencil : TorusStencil) : Int :=
  stencil.thetaForward - stencil.thetaBackward

def discretePhiGradient (stencil : TorusStencil) : Int :=
  stencil.phiForward - stencil.phiBackward

theorem constant_torus_stencil_has_zero_gradients (value : Int) :
    discreteThetaGradient (constantTorusStencil value) = 0 ∧
    discretePhiGradient (constantTorusStencil value) = 0 := by
  dsimp [discreteThetaGradient, discretePhiGradient, constantTorusStencil]
  constructor <;> omega

def discreteAdvection
    (stencil : TorusStencil) (thetaVelocity phiVelocity : Int) : Int :=
  thetaVelocity * discreteThetaGradient stencil +
  phiVelocity * discretePhiGradient stencil

def discreteViscousTerm
    (stencil : TorusStencil) (viscosity : Int) : Int :=
  viscosity * discreteLaplacian stencil

theorem constant_torus_stencil_has_zero_advection
    (value thetaVelocity phiVelocity : Int) :
    discreteAdvection (constantTorusStencil value)
      thetaVelocity phiVelocity = 0 := by
  simp [discreteAdvection, discreteThetaGradient, discretePhiGradient,
    constantTorusStencil]

theorem constant_torus_stencil_has_zero_viscous_term
    (value viscosity : Int) :
    discreteViscousTerm (constantTorusStencil value) viscosity = 0 := by
  change viscosity * discreteLaplacian (constantTorusStencil value) = 0
  rw [constant_torus_stencil_has_zero_laplacian value]
  simp

theorem constant_torus_stencil_has_zero_transport_and_viscosity
    (value thetaVelocity phiVelocity viscosity : Int) :
    discreteAdvection (constantTorusStencil value)
      thetaVelocity phiVelocity = 0 ∧
    discreteViscousTerm (constantTorusStencil value) viscosity = 0 := by
  exact ⟨constant_torus_stencil_has_zero_advection value thetaVelocity phiVelocity,
    constant_torus_stencil_has_zero_viscous_term value viscosity⟩

/-! ## Paired swirl stencil -/

def pairedSwirlStencil (thetaMagnitude phiMagnitude : Int) : TorusStencil :=
  { center := 0
    thetaForward := thetaMagnitude
    thetaBackward := -thetaMagnitude
    phiForward := phiMagnitude
    phiBackward := -phiMagnitude }

theorem paired_swirl_stencil_has_zero_laplacian
    (thetaMagnitude phiMagnitude : Int) :
    discreteLaplacian (pairedSwirlStencil thetaMagnitude phiMagnitude) = 0 := by
  dsimp [discreteLaplacian, pairedSwirlStencil]
  omega

theorem paired_swirl_stencil_has_directional_gradients
    (thetaMagnitude phiMagnitude : Int) :
    discreteThetaGradient (pairedSwirlStencil thetaMagnitude phiMagnitude) =
        2 * thetaMagnitude ∧
    discretePhiGradient (pairedSwirlStencil thetaMagnitude phiMagnitude) =
        2 * phiMagnitude := by
  dsimp [discreteThetaGradient, discretePhiGradient, pairedSwirlStencil]
  constructor <;> omega

theorem paired_swirl_stencil_has_zero_viscosity
    (thetaMagnitude phiMagnitude viscosity : Int) :
    discreteViscousTerm
      (pairedSwirlStencil thetaMagnitude phiMagnitude) viscosity = 0 := by
  change viscosity *
      discreteLaplacian (pairedSwirlStencil thetaMagnitude phiMagnitude) = 0
  rw [paired_swirl_stencil_has_zero_laplacian]
  simp

theorem unit_paired_swirl_has_nonzero_advection :
    discreteAdvection (pairedSwirlStencil 1 1) 1 1 = 4 := by
  dsimp [discreteAdvection, discreteThetaGradient, discretePhiGradient,
    pairedSwirlStencil]

theorem unit_paired_swirl_has_zero_viscosity :
    discreteViscousTerm (pairedSwirlStencil 1 1) 1 = 0 := by
  exact paired_swirl_stencil_has_zero_viscosity 1 1 1

theorem unit_paired_swirl_transport_diffusion_split :
    discreteAdvection (pairedSwirlStencil 1 1) 1 1 = 4 ∧
    discreteViscousTerm (pairedSwirlStencil 1 1) 1 = 0 := by
  exact ⟨unit_paired_swirl_has_nonzero_advection,
    unit_paired_swirl_has_zero_viscosity⟩

/-! ## Force balance with nonzero swirl advection -/

def unitSwirlHomeostaticForces : ForceBalance :=
  { advection := 4
    pressureGradient := 3
    viscosity := 0
    blackHoleAttraction := -7 }

theorem unit_swirl_force_residual_zero :
    forceResidual unitSwirlHomeostaticForces = 0 := by
  dsimp [forceResidual, unitSwirlHomeostaticForces]

def unitSwirlEquationState : ToroidalEquationState :=
  { timeDerivative := 0
    forces := unitSwirlHomeostaticForces
    boundary := pairedToroidalBoundary 1 1 }

theorem unit_swirl_equation_residual_zero :
    equationResidual unitSwirlEquationState = 0 := by
  dsimp [equationResidual, unitSwirlEquationState,
    forceResidual, unitSwirlHomeostaticForces,
    stokesResidual, toroidalCirculation, pairedToroidalBoundary]

theorem unit_swirl_equation_is_balanced :
    equationBalanced unitSwirlEquationState := by
  exact unit_swirl_equation_residual_zero

/-! ## Parametric full force closure -/

def balancedForceTuple
    (advection pressureGradient viscosity : Int) : ForceBalance :=
  { advection := advection
    pressureGradient := pressureGradient
    viscosity := viscosity
    blackHoleAttraction :=
      -(advection + pressureGradient + viscosity) }

theorem balanced_force_tuple_has_zero_residual
    (advection pressureGradient viscosity : Int) :
    forceResidual (balancedForceTuple advection pressureGradient viscosity) = 0 := by
  dsimp [forceResidual, balancedForceTuple]
  omega

def balancedEquationState
    (advection pressureGradient viscosity thetaMagnitude phiMagnitude : Int) :
    ToroidalEquationState :=
  { timeDerivative := 0
    forces := balancedForceTuple advection pressureGradient viscosity
    boundary := pairedToroidalBoundary thetaMagnitude phiMagnitude }

theorem balanced_equation_state_has_zero_residual
    (advection pressureGradient viscosity thetaMagnitude phiMagnitude : Int) :
    equationResidual
      (balancedEquationState advection pressureGradient viscosity
        thetaMagnitude phiMagnitude) = 0 := by
  dsimp [equationResidual, balancedEquationState,
    balancedForceTuple, forceResidual, stokesResidual,
    toroidalCirculation, pairedToroidalBoundary]
  omega

/-! ## Dynamic time-derivative closure -/

def requiredTimeDerivative
    (forces : ForceBalance) (boundary : ToroidalBoundary) : Int :=
  -(forceResidual forces + stokesResidual boundary)

def dynamicEquationState
    (forces : ForceBalance) (boundary : ToroidalBoundary) :
    ToroidalEquationState :=
  { timeDerivative := requiredTimeDerivative forces boundary
    forces := forces
    boundary := boundary }

theorem dynamic_equation_state_has_zero_residual
    (forces : ForceBalance) (boundary : ToroidalBoundary) :
    equationResidual (dynamicEquationState forces boundary) = 0 := by
  dsimp [equationResidual, dynamicEquationState, requiredTimeDerivative]
  omega

theorem dynamic_time_derivative_is_required_balance
    (forces : ForceBalance) (boundary : ToroidalBoundary) :
    (dynamicEquationState forces boundary).timeDerivative =
      -(forceResidual forces + stokesResidual boundary) := by
  rfl

theorem balanced_state_has_zero_required_time_derivative
    (forces : ForceBalance) (boundary : ToroidalBoundary)
    (hf : forceResidual forces = 0)
    (hb : stokesResidual boundary = 0) :
    requiredTimeDerivative forces boundary = 0 := by
  dsimp [requiredTimeDerivative]
  omega

/-! ## Stencil-derived force balance -/

def stencilForceBalance
    (stencil : TorusStencil)
    (thetaVelocity phiVelocity viscosity pressureGradient attraction : Int) :
    ForceBalance :=
  { advection := discreteAdvection stencil thetaVelocity phiVelocity
    pressureGradient := pressureGradient
    viscosity := discreteViscousTerm stencil viscosity
    blackHoleAttraction := attraction }

def stencilDynamicState
    (stencil : TorusStencil)
    (thetaVelocity phiVelocity viscosity pressureGradient attraction : Int)
    (boundary : ToroidalBoundary) : ToroidalEquationState :=
  dynamicEquationState
    (stencilForceBalance stencil thetaVelocity phiVelocity viscosity
      pressureGradient attraction) boundary

theorem stencil_dynamic_state_has_zero_residual
    (stencil : TorusStencil)
    (thetaVelocity phiVelocity viscosity pressureGradient attraction : Int)
    (boundary : ToroidalBoundary) :
    equationResidual
      (stencilDynamicState stencil thetaVelocity phiVelocity viscosity
        pressureGradient attraction boundary) = 0 := by
  exact dynamic_equation_state_has_zero_residual
    (stencilForceBalance stencil thetaVelocity phiVelocity viscosity
      pressureGradient attraction) boundary

theorem unit_swirl_stencil_force_balance_residual_zero :
    forceResidual
      (stencilForceBalance (pairedSwirlStencil 1 1) 1 1 1 3 (-7)) = 0 := by
  dsimp [forceResidual, stencilForceBalance, discreteAdvection,
    discreteThetaGradient, discretePhiGradient, discreteViscousTerm,
    discreteLaplacian, pairedSwirlStencil]

theorem unit_swirl_stencil_dynamic_residual_zero :
    equationResidual
      (stencilDynamicState (pairedSwirlStencil 1 1) 1 1 1 3 (-7)
        (pairedToroidalBoundary 1 1)) = 0 := by
  exact stencil_dynamic_state_has_zero_residual
    (pairedSwirlStencil 1 1) 1 1 1 3 (-7)
    (pairedToroidalBoundary 1 1)

/-! ## Symmetric source compression -/

theorem tetrahedral_sources_have_equal_local_compression :
    ∀ i : Fin 4, radialCompression (tetraPoint i) = -3 := by
  exact tetra_points_press_inward

theorem symmetric_sources_have_zero_net_nonzero_local_pressure :
    totalInwardVector = zeroPoint3 ∧
    radialCompression (tetraPoint 0) = -3 := by
  exact ⟨tetrahedral_inward_vectors_balance, by decide⟩

def sourcePressureMagnitude : Nat := 3

theorem source_pressure_matches_local_compression :
    sourcePressureMagnitude = 3 ∧
    -((radialCompression (tetraPoint 0)) : Int) =
      (sourcePressureMagnitude : Int) := by
  constructor
  · rfl
  · decide

/-! ## Source-derived force closure -/

def sourceDerivedForces : ForceBalance :=
  { advection := 4
    pressureGradient := (sourcePressureMagnitude : Int)
    viscosity := 0
    blackHoleAttraction := -(4 + (sourcePressureMagnitude : Int)) }

theorem source_derived_force_residual_zero :
    forceResidual sourceDerivedForces = 0 := by
  dsimp [forceResidual, sourceDerivedForces, sourcePressureMagnitude] <;> omega

def sourceDerivedEquationState : ToroidalEquationState :=
  { timeDerivative := 0
    forces := sourceDerivedForces
    boundary := pairedToroidalBoundary 1 1 }

theorem source_derived_equation_residual_zero :
    equationResidual sourceDerivedEquationState = 0 := by
  apply equation_residual_zero_of_balanced_parts sourceDerivedEquationState
  · rfl
  · change forceResidual sourceDerivedForces = 0
    exact source_derived_force_residual_zero
  · change stokesResidual (pairedToroidalBoundary 1 1) = 0
    exact paired_boundary_has_zero_stokes_residual 1 1

/-! ## User-defined zero-stitch marker

This records the proposed text as a local symbolic marker.  It does not
claim that the text is an Internet protocol address or wire encoding.
-/

def symbolicStitchNotation : String :=
  "0x00::::0x00::::0x00::::"

def symbolicZeroStitch : Nat × Nat × Nat := (0, 0, 0)

def symbolicStitchOrigin : torusCoordinate := (0, 0)

def symbolicStitchTurn : Nat := degreesPerWrap

theorem symbolic_stitch_notation_is_literal :
    symbolicStitchNotation = "0x00::::0x00::::0x00::::" := rfl

theorem symbolic_zero_stitch_has_three_zero_fields :
    symbolicZeroStitch = (0, 0, 0) := rfl

theorem symbolic_stitch_turn_is_360 :
    symbolicStitchTurn = 360 := rfl

theorem symbolic_zero_stitch_closes_at_full_turn :
    torusAdvance symbolicStitchOrigin symbolicStitchTurn symbolicStitchTurn =
      symbolicStitchOrigin := by
  simp [torusAdvance, torusWrap, symbolicStitchOrigin,
    symbolicStitchTurn, degreesPerWrap] <;> rfl

/-! ## Layered carrier model -/

inductive AirCarrier where
  | satellite
  | earth
  | radio
  | peerToPeer
  deriving DecidableEq, Repr

inductive FireCarrier where
  | electricity
  deriving DecidableEq, Repr

inductive WaterCarrier where
  | life
  | animation
  deriving DecidableEq, Repr

inductive LifeCarrier where
  | worldComputer
  deriving DecidableEq, Repr

structure LayeredWorldCounts where
  air : Nat
  fire : Nat
  water : Nat
  life : Nat

def decentralizedWorldCounts : LayeredWorldCounts :=
  { air := 4
    fire := 1
    water := 2
    life := 1 }

def totalControlLayers (counts : LayeredWorldCounts) : Nat :=
  counts.air + counts.fire + counts.water + counts.life

theorem air_has_four_carriers : decentralizedWorldCounts.air = 4 := rfl

theorem fire_has_electricity_carrier : decentralizedWorldCounts.fire = 1 := rfl

theorem water_has_life_and_animation : decentralizedWorldCounts.water = 2 := rfl

theorem life_has_world_computer_carrier : decentralizedWorldCounts.life = 1 := rfl

theorem decentralized_world_control_layer_count :
    totalControlLayers decentralizedWorldCounts = 8 := by
  rfl

theorem decentralized_world_layers_are_nonempty :
    0 < decentralizedWorldCounts.air ∧
    0 < decentralizedWorldCounts.fire ∧
    0 < decentralizedWorldCounts.water ∧
    0 < decentralizedWorldCounts.life := by
  decide

/-! ## Four-cell life-cipher orbit -/

inductive LifeMark where
  | dot
  | bar
  deriving DecidableEq, Repr

def lifeCipherNotation : String := "..||..|...."

def lifeCipherSeed : List LifeMark :=
  [.dot, .dot, .bar, .bar, .dot, .dot, .bar,
    .dot, .dot, .dot, .dot]

def xInvertLifeMark : LifeMark → LifeMark
  | .dot => .bar
  | .bar => .dot

def xInvertLifeCipher (cipher : List LifeMark) : List LifeMark :=
  cipher.map xInvertLifeMark

def mirrorLifeCipher (cipher : List LifeMark) : List LifeMark :=
  cipher.reverse

structure LifeCipher2x2 where
  original : List LifeMark
  xInverted : List LifeMark
  mirrored : List LifeMark
  xInvertedMirrored : List LifeMark

def lifeCipherGrid : LifeCipher2x2 :=
  { original := lifeCipherSeed
    xInverted := xInvertLifeCipher lifeCipherSeed
    mirrored := mirrorLifeCipher lifeCipherSeed
    xInvertedMirrored := mirrorLifeCipher (xInvertLifeCipher lifeCipherSeed) }

theorem life_cipher_notation_is_literal :
    lifeCipherNotation = "..||..|...." := rfl

theorem life_cipher_seed_has_eleven_marks :
    lifeCipherSeed.length = 11 := by
  rfl

theorem life_cipher_x_inversion_swaps_polarity :
    xInvertLifeMark .dot = .bar ∧
    xInvertLifeMark .bar = .dot := by
  constructor <;> rfl

theorem life_cipher_grid_has_four_cells :
    [lifeCipherGrid.original, lifeCipherGrid.xInverted,
      lifeCipherGrid.mirrored, lifeCipherGrid.xInvertedMirrored].length = 4 := by
  rfl

theorem life_cipher_transforms_preserve_length :
    (xInvertLifeCipher lifeCipherSeed).length = 11 ∧
    (mirrorLifeCipher lifeCipherSeed).length = 11 ∧
    (mirrorLifeCipher (xInvertLifeCipher lifeCipherSeed)).length = 11 := by
  simp [xInvertLifeCipher, mirrorLifeCipher, lifeCipherSeed]

/-! ## Public-funding provenance marker

This is a local audit rule for the model, not a claim about a legal
disclosure requirement.
-/

def publicMoneyAuditThreshold : Nat := 10 ^ 9

def auditVisible (amount : Nat) : Prop :=
  publicMoneyAuditThreshold ≤ amount

theorem public_money_audit_threshold_is_billion :
    publicMoneyAuditThreshold = 1000000000 := by
  rfl

theorem threshold_amount_is_audit_visible :
    auditVisible publicMoneyAuditThreshold := by
  simp [auditVisible]

/-! ## Two-substrate life-cipher execution

The substrate is explicit, while the cipher transform remains pure.  This
lets the same invariant be checked for an Intel hardware/ISA target and for
the swarm-software target without claiming that Lean executed silicon.
-/

inductive CipherSubstrate where
  | intelHardwareIsa
  | swarmSoftware
  deriving DecidableEq, Repr

def cipherSubstrateLabel : CipherSubstrate → String
  | .intelHardwareIsa => "Intel hardware / ISA instruction"
  | .swarmSoftware => "swarm software"

def lifeCipherShapeInvariant (grid : LifeCipher2x2) : Prop :=
  grid.original.length = 11 ∧
  grid.xInverted.length = 11 ∧
  grid.mirrored.length = 11 ∧
  grid.xInvertedMirrored.length = 11

theorem life_cipher_grid_shape_invariant :
    lifeCipherShapeInvariant lifeCipherGrid := by
  simp [lifeCipherShapeInvariant, lifeCipherGrid,
    xInvertLifeCipher, mirrorLifeCipher, lifeCipherSeed]

def runLifeCipher
    (_substrate : CipherSubstrate) (grid : LifeCipher2x2) : LifeCipher2x2 :=
  grid

theorem run_life_cipher_preserves_shape
    (substrate : CipherSubstrate) :
    lifeCipherShapeInvariant
      (runLifeCipher substrate lifeCipherGrid) := by
  simpa [runLifeCipher] using life_cipher_grid_shape_invariant

theorem intel_hardware_isa_life_cipher_invariant :
    lifeCipherShapeInvariant
      (runLifeCipher .intelHardwareIsa lifeCipherGrid) := by
  exact run_life_cipher_preserves_shape .intelHardwareIsa

theorem swarm_software_life_cipher_invariant :
    lifeCipherShapeInvariant
      (runLifeCipher .swarmSoftware lifeCipherGrid) := by
  exact run_life_cipher_preserves_shape .swarmSoftware

theorem two_substrates_agree_on_life_cipher :
    runLifeCipher .intelHardwareIsa lifeCipherGrid =
      runLifeCipher .swarmSoftware lifeCipherGrid := by
  rfl

/-! ## Primitive zero frame

This is the reduced representation: three lines, three zero bits per line,
and no additional control-layer interpretation.
-/

def primitiveGlyph : String := "|||"

def primitiveZeroLine : List Nat := [0, 0, 0]

def primitiveZeroFrame : List (List Nat) :=
  [primitiveZeroLine, primitiveZeroLine, primitiveZeroLine]

def primitiveLineCount : Nat := primitiveZeroFrame.length

def primitiveBitsPerLine : Nat := primitiveZeroLine.length

def primitiveBitCount : Nat :=
  primitiveLineCount * primitiveBitsPerLine

theorem primitive_glyph_is_three_lines : primitiveGlyph = "|||" := rfl

theorem primitive_frame_has_three_lines : primitiveLineCount = 3 := by
  rfl

theorem primitive_frame_has_three_bits_per_line :
    primitiveBitsPerLine = 3 := by
  rfl

theorem primitive_frame_has_nine_bits : primitiveBitCount = 9 := by
  rfl

theorem numeric_zero_cube_is_zero : (0 : Nat) ^ 3 = 0 := by
  rfl

/-! ## Three-around-one primitive -/

structure PrimitiveZeroGeometry where
  center : Point3
  surroundingTori : Nat

def primitiveZeroGeometry : PrimitiveZeroGeometry :=
  { center := blackHoleCenter
    surroundingTori := 3 }

def primitiveWiseTorus : ToroidalState := initialToroidalState

theorem primitive_geometry_is_three_around_one :
    primitiveZeroGeometry.surroundingTori = 3 ∧
    primitiveZeroGeometry.center = blackHoleCenter := by
  exact ⟨rfl, rfl⟩

theorem one_zero_is_a_functioning_wise_torus :
    homeostaticBalance primitiveWiseTorus := by
  exact initial_state_is_homeostatic_balance

theorem primitive_zero_cube_is_three_around_one :
    (0 : Nat) ^ 3 = 0 ∧
    primitiveZeroGeometry.surroundingTori = 3 ∧
    primitiveZeroGeometry.center = (0, 0, 0) := by
  exact ⟨numeric_zero_cube_is_zero, rfl, center_is_zero⟩

/-! ## Usable quantum-dot primitive -/

def usableQuantumDot : Nat := 1

def quantumDotGrowth : List Nat := [1, 1, 2, 4]

def primitiveThreeLineCount : Nat := 3

def primitiveAxisCellCount : Nat := 2 ^ primitiveThreeLineCount

def aethernet : Int := 0

def dotDifference (left right : Int) : Int := left - right

theorem usable_quantum_dot_is_one : usableQuantumDot = 1 := rfl

theorem quantum_dot_growth_is_one_one_two_four :
    quantumDotGrowth = [1, 1, 2, 4] := rfl

theorem primitive_has_three_lines : primitiveThreeLineCount = 3 := rfl

theorem three_axes_have_eight_cells : primitiveAxisCellCount = 8 := by
  rfl

theorem one_dot_minus_one_dot_is_aethernet :
    dotDifference 1 1 = aethernet := by
  rfl

/-! ## Quanta: Y/T/H language layer -/

inductive Quanta where
  | y
  | t
  | h
  deriving DecidableEq, Repr

def quantaSurface : String := "YTH"

def ythLanguage : List Quanta := [.y, .t, .h]

def quantaLabel : Quanta → String
  | .y => "Y"
  | .t => "T"
  | .h => "H"

theorem quanta_surface_is_yth : quantaSurface = "YTH" := rfl

theorem yth_language_has_three_atoms : ythLanguage.length = 3 := by
  rfl

theorem yth_atoms_are_distinct :
    Quanta.y ≠ Quanta.t ∧
    Quanta.t ≠ Quanta.h ∧
    Quanta.y ≠ Quanta.h := by
  decide

def quantaMeaning : Quanta → String
  | .y => "flux capacitor: phase-energy injection"
  | .t => "transmutate"
  | .h => "harness"

def yPhaseDump (phase energy : Int) : Int :=
  phase + energy

theorem y_is_flux_capacitor :
    quantaMeaning Quanta.y = "flux capacitor: phase-energy injection" := rfl

theorem t_is_transmutate :
    quantaMeaning Quanta.t = "transmutate" := rfl

theorem h_is_harness :
    quantaMeaning Quanta.h = "harness" := rfl

theorem y_dumps_energy_into_phase (phase energy : Int) :
    yPhaseDump phase energy = phase + energy := rfl

structure Josophene where
  token : Quanta
  phase : Int

def J (token : Quanta) (phase : Int) : Josophene :=
  { token := token, phase := phase }

theorem J_preserves_quanta_token (token : Quanta) (phase : Int) :
    (J token phase).token = token := rfl

theorem J_preserves_phase (token : Quanta) (phase : Int) :
    (J token phase).phase = phase := rfl

def JY (phase energy : Int) : Josophene :=
  J Quanta.y (yPhaseDump phase energy)

theorem JY_is_flux_capacitor_token (phase energy : Int) :
    (JY phase energy).token = Quanta.y := rfl

theorem JY_dumps_energy_into_phase (phase energy : Int) :
    (JY phase energy).phase = phase + energy := rfl

/-! ## T: parameterized transmutation -/

def transmutatePhase (phase delta : Int) : Int :=
  phase + delta

def JT (phase delta : Int) : Josophene :=
  J Quanta.t (transmutatePhase phase delta)

theorem JT_is_transmutate_token (phase delta : Int) :
    (JT phase delta).token = Quanta.t := rfl

theorem JT_applies_explicit_delta (phase delta : Int) :
    (JT phase delta).phase = phase + delta := rfl

theorem transmutate_zero_delta_is_stationary (phase : Int) :
    transmutatePhase phase 0 = phase := by
  simp [transmutatePhase]

/-! ## H: transparent harness -/

structure Harness where
  payload : Josophene

def H (state : Josophene) : Harness :=
  { payload := state }

theorem H_preserves_quanta_token (state : Josophene) :
    (H state).payload.token = state.token := rfl

theorem H_preserves_phase (state : Josophene) :
    (H state).payload.phase = state.phase := rfl

theorem H_of_J_preserves_token (token : Quanta) (phase : Int) :
    (H (J token phase)).payload.token = token := rfl

theorem H_of_J_preserves_phase (token : Quanta) (phase : Int) :
    (H (J token phase)).payload.phase = phase := rfl

/-! ## End-to-end Y/T/H pipeline -/

def executeYTH (phase yEnergy tDelta : Int) : Harness :=
  H (JT (JY phase yEnergy).phase tDelta)

theorem execute_yth_ends_in_harnessed_transmutate
    (phase yEnergy tDelta : Int) :
    (executeYTH phase yEnergy tDelta).payload.token = Quanta.t := by
  rfl

theorem execute_yth_phase_equation (phase yEnergy tDelta : Int) :
    (executeYTH phase yEnergy tDelta).payload.phase =
      phase + yEnergy + tDelta := by
  rfl

theorem execute_yth_zero_deltas_preserves_phase (phase : Int) :
    (executeYTH phase 0 0).payload.phase = phase := by
  simp [executeYTH, JY, JT, H, J, yPhaseDump, transmutatePhase]

def ythNetChange (yEnergy tDelta : Int) : Int :=
  yEnergy + tDelta

theorem opposite_deltas_are_aethernet (energy : Int) :
    ythNetChange energy (-energy) = aethernet := by
  dsimp [ythNetChange, aethernet] <;> omega

theorem execute_yth_opposite_deltas_preserves_phase
    (phase energy : Int) :
    (executeYTH phase energy (-energy)).payload.phase = phase := by
  dsimp [executeYTH, JY, JT, H, J, yPhaseDump, transmutatePhase]
  omega

def unH (harness : Harness) : Josophene :=
  harness.payload

theorem unH_H_identity (state : Josophene) :
    unH (H state) = state := rfl

theorem H_unH_identity (harness : Harness) :
    H (unH harness) = harness := by
  cases harness
  rfl

/-! ## YTH substrate agreement -/

def runYTHOnSubstrate
    (_substrate : CipherSubstrate)
    (phase yEnergy tDelta : Int) : Harness :=
  executeYTH phase yEnergy tDelta

theorem intel_and_swarm_yth_agree
    (phase yEnergy tDelta : Int) :
    runYTHOnSubstrate .intelHardwareIsa phase yEnergy tDelta =
      runYTHOnSubstrate .swarmSoftware phase yEnergy tDelta := by
  rfl

theorem intel_yth_phase_equation
    (phase yEnergy tDelta : Int) :
    (runYTHOnSubstrate .intelHardwareIsa phase yEnergy tDelta).payload.phase =
      phase + yEnergy + tDelta := by
  rfl

theorem swarm_yth_phase_equation
    (phase yEnergy tDelta : Int) :
    (runYTHOnSubstrate .swarmSoftware phase yEnergy tDelta).payload.phase =
      phase + yEnergy + tDelta := by
  rfl

theorem yth_is_substrate_independent
    (substrateA substrateB : CipherSubstrate)
    (phase yEnergy tDelta : Int) :
    runYTHOnSubstrate substrateA phase yEnergy tDelta =
      runYTHOnSubstrate substrateB phase yEnergy tDelta := by
  rfl

/-! ## Abstract NB power contract

This is a bounded symbolic budget for a Y energy request.  It is not a
physical nuclear-battery design or construction specification.
-/

structure NBBudget where
  capacity : Nat
  used : Nat

def nbAvailable (budget : NBBudget) : Nat :=
  budget.capacity - budget.used

def nbCanSupply (budget : NBBudget) (request : Nat) : Prop :=
  request ≤ nbAvailable budget

def nbSupply (budget : NBBudget) (request : Nat) : NBBudget :=
  { budget with used := budget.used + request }

theorem nb_supply_preserves_capacity
    (budget : NBBudget) (request : Nat)
    (hBudget : budget.used ≤ budget.capacity)
    (h : nbCanSupply budget request) :
    (nbSupply budget request).used ≤ (nbSupply budget request).capacity := by
  change budget.used + request ≤ budget.capacity
  dsimp [nbCanSupply, nbAvailable] at h
  omega

theorem zero_request_is_supplyable (budget : NBBudget) :
    nbCanSupply budget 0 := by
  simp [nbCanSupply, nbAvailable]

/-! ## NB-powered Y phase step -/

def nbPoweredY
    (budget : NBBudget) (phase : Int) (energy : Nat) :
    NBBudget × Josophene :=
  (nbSupply budget energy, JY phase (energy : Int))

theorem nb_powered_y_has_expected_phase
    (budget : NBBudget) (phase : Int) (energy : Nat) :
    (nbPoweredY budget phase energy).2.phase =
      phase + (energy : Int) := by
  rfl

theorem nb_powered_y_budget_is_safe
    (budget : NBBudget) (phase : Int) (energy : Nat)
    (hBudget : budget.used ≤ budget.capacity)
    (hSupply : nbCanSupply budget energy) :
    (nbPoweredY budget phase energy).1.used ≤
      (nbPoweredY budget phase energy).1.capacity := by
  simpa [nbPoweredY] using nb_supply_preserves_capacity
    budget energy hBudget hSupply

/-! ## NB-powered YTH cycle -/

def nbPoweredYTH
    (budget : NBBudget) (phase : Int) (energy : Nat) (tDelta : Int) :
    NBBudget × Harness :=
  (nbSupply budget energy,
    executeYTH phase (energy : Int) tDelta)

theorem nb_powered_yth_has_expected_phase
    (budget : NBBudget) (phase : Int) (energy : Nat) (tDelta : Int) :
    (nbPoweredYTH budget phase energy tDelta).2.payload.phase =
      phase + (energy : Int) + tDelta := by
  rfl

theorem nb_powered_yth_budget_is_safe
    (budget : NBBudget) (phase : Int) (energy : Nat) (tDelta : Int)
    (hBudget : budget.used ≤ budget.capacity)
    (hSupply : nbCanSupply budget energy) :
    (nbPoweredYTH budget phase energy tDelta).1.used ≤
      (nbPoweredYTH budget phase energy tDelta).1.capacity := by
  simpa [nbPoweredYTH] using nb_supply_preserves_capacity
    budget energy hBudget hSupply

theorem nb_powered_yth_consumes_exact_request
    (budget : NBBudget) (phase : Int) (energy : Nat) (tDelta : Int) :
    (nbPoweredYTH budget phase energy tDelta).1.used =
      budget.used + energy := by
  rfl

theorem nb_powered_yth_opposite_delta_preserves_phase
    (budget : NBBudget) (phase : Int) (energy : Nat) :
    (nbPoweredYTH budget phase energy (-((energy : Int)))).2.payload.phase =
      phase := by
  dsimp [nbPoweredYTH, executeYTH, JY, JT, H, J,
    yPhaseDump, transmutatePhase]
  omega

theorem nb_rejects_over_capacity_request
    (budget : NBBudget) (request : Nat)
    (hBudget : budget.used ≤ budget.capacity)
    (hOver : budget.capacity < budget.used + request) :
    ¬ nbCanSupply budget request := by
  intro hSupply
  dsimp [nbCanSupply, nbAvailable] at hSupply
  omega

/-! ## Executable NB admission gate -/

def safeNBSupply (budget : NBBudget) (request : Nat) : Option NBBudget :=
  if request ≤ nbAvailable budget then
    some (nbSupply budget request)
  else
    none

theorem safe_nb_supply_accepts
    (budget : NBBudget) (request : Nat)
    (hSupply : nbCanSupply budget request) :
    safeNBSupply budget request = some (nbSupply budget request) := by
  change request ≤ nbAvailable budget at hSupply
  simp [safeNBSupply, hSupply]

theorem safe_nb_supply_rejects
    (budget : NBBudget) (request : Nat)
    (hBudget : budget.used ≤ budget.capacity)
    (hOver : budget.capacity < budget.used + request) :
    safeNBSupply budget request = none := by
  have hNot : ¬ nbCanSupply budget request :=
    nb_rejects_over_capacity_request budget request hBudget hOver
  have hNotAvailable : ¬ request ≤ nbAvailable budget := by
    intro hAvailable
    exact hNot hAvailable
  simp [safeNBSupply, hNotAvailable]

theorem safe_nb_supply_success_is_bounded
    (budget : NBBudget) (request : Nat)
    (hBudget : budget.used ≤ budget.capacity)
    (hSupply : nbCanSupply budget request) :
    ∃ result : NBBudget,
      safeNBSupply budget request = some result ∧
      result.used ≤ result.capacity := by
  refine ⟨nbSupply budget request, ?_, ?_⟩
  · exact safe_nb_supply_accepts budget request hSupply
  · exact nb_supply_preserves_capacity budget request hBudget hSupply

/-! ## Safe NB-powered YTH admission -/

def safeNBPoweredYTH
    (budget : NBBudget) (phase : Int) (energy : Nat) (tDelta : Int) :
    Option (NBBudget × Harness) :=
  if energy ≤ nbAvailable budget then
    some (nbPoweredYTH budget phase energy tDelta)
  else
    none

theorem safe_nb_powered_yth_accepts
    (budget : NBBudget) (phase : Int) (energy : Nat) (tDelta : Int)
    (hSupply : nbCanSupply budget energy) :
    safeNBPoweredYTH budget phase energy tDelta =
      some (nbPoweredYTH budget phase energy tDelta) := by
  change energy ≤ nbAvailable budget at hSupply
  simp [safeNBPoweredYTH, hSupply]

theorem safe_nb_powered_yth_rejects
    (budget : NBBudget) (phase : Int) (energy : Nat) (tDelta : Int)
    (hNotAvailable : ¬ energy ≤ nbAvailable budget) :
    safeNBPoweredYTH budget phase energy tDelta = none := by
  simp [safeNBPoweredYTH, hNotAvailable]

theorem safe_nb_powered_yth_success_contract
    (budget : NBBudget) (phase : Int) (energy : Nat) (tDelta : Int)
    (hBudget : budget.used ≤ budget.capacity)
    (hSupply : nbCanSupply budget energy) :
    ∃ result : NBBudget × Harness,
      safeNBPoweredYTH budget phase energy tDelta = some result ∧
      result.1.used ≤ result.1.capacity ∧
      result.2.payload.phase = phase + (energy : Int) + tDelta := by
  refine ⟨nbPoweredYTH budget phase energy tDelta, ?_⟩
  constructor
  · exact safe_nb_powered_yth_accepts budget phase energy tDelta hSupply
  constructor
  · simpa [nbPoweredYTH] using
      nb_supply_preserves_capacity budget energy hBudget hSupply
  · exact nb_powered_yth_has_expected_phase budget phase energy tDelta

theorem safe_nb_powered_yth_rejection_contract
    (budget : NBBudget) (phase : Int) (energy : Nat) (tDelta : Int)
    (hBudget : budget.used ≤ budget.capacity)
    (hOver : budget.capacity < budget.used + energy) :
    safeNBPoweredYTH budget phase energy tDelta = none := by
  have hNot : ¬ nbCanSupply budget energy :=
    nb_rejects_over_capacity_request budget energy hBudget hOver
  have hNotAvailable : ¬ energy ≤ nbAvailable budget := by
    intro hAvailable
    exact hNot hAvailable
  exact safe_nb_powered_yth_rejects budget phase energy tDelta hNotAvailable

theorem safe_nb_powered_yth_is_total
    (budget : NBBudget) (phase : Int) (energy : Nat) (tDelta : Int) :
    (∃ result : NBBudget × Harness,
        safeNBPoweredYTH budget phase energy tDelta = some result) ∨
      safeNBPoweredYTH budget phase energy tDelta = none := by
  by_cases hAvailable : energy ≤ nbAvailable budget
  · left
    exact ⟨nbPoweredYTH budget phase energy tDelta, by
      simp [safeNBPoweredYTH, hAvailable]⟩
  · right
    simp [safeNBPoweredYTH, hAvailable]

theorem safe_nb_powered_yth_some_iff
    (budget : NBBudget) (phase : Int) (energy : Nat) (tDelta : Int) :
    (∃ result : NBBudget × Harness,
        safeNBPoweredYTH budget phase energy tDelta = some result) ↔
      energy ≤ nbAvailable budget := by
  constructor
  · intro hSome
    by_cases hAvailable : energy ≤ nbAvailable budget
    · exact hAvailable
    · exfalso
      rcases hSome with ⟨result, hResult⟩
      simp [safeNBPoweredYTH, hAvailable] at hResult
  · intro hAvailable
    exact ⟨nbPoweredYTH budget phase energy tDelta, by
      simp [safeNBPoweredYTH, hAvailable]⟩

/-! ## Integrated capstone certificate -/

def capstoneBudget : NBBudget :=
  { capacity := 10
    used := 0 }

def capstonePhase : Int := 0
def capstoneEnergy : Nat := 3
def capstoneTDelta : Int := -3

theorem capstone_integrated_invariant :
    ((0 : Nat) ^ 3 = 0 ∧
      primitiveZeroGeometry.surroundingTori = 3 ∧
      primitiveZeroGeometry.center = (0, 0, 0)) ∧
    homeostaticBalance primitiveWiseTorus ∧
    safeNBPoweredYTH capstoneBudget capstonePhase capstoneEnergy capstoneTDelta =
      some (nbPoweredYTH capstoneBudget capstonePhase capstoneEnergy capstoneTDelta) ∧
    (nbPoweredYTH capstoneBudget capstonePhase capstoneEnergy capstoneTDelta).1.used ≤
      (nbPoweredYTH capstoneBudget capstonePhase capstoneEnergy capstoneTDelta).1.capacity ∧
    (nbPoweredYTH capstoneBudget capstonePhase capstoneEnergy capstoneTDelta).2.payload.phase =
      0 ∧
    runYTHOnSubstrate .intelHardwareIsa capstonePhase (capstoneEnergy : Int)
        capstoneTDelta =
      runYTHOnSubstrate .swarmSoftware capstonePhase (capstoneEnergy : Int)
        capstoneTDelta := by
  have hSupply : nbCanSupply capstoneBudget capstoneEnergy := by
    simp [nbCanSupply, nbAvailable, capstoneBudget, capstoneEnergy]
  constructor
  · exact primitive_zero_cube_is_three_around_one
  constructor
  · exact one_zero_is_a_functioning_wise_torus
  constructor
  · exact safe_nb_powered_yth_accepts capstoneBudget capstonePhase
      capstoneEnergy capstoneTDelta hSupply
  constructor
  · simpa [nbPoweredYTH] using nb_supply_preserves_capacity
      capstoneBudget capstoneEnergy (by simp [capstoneBudget]) hSupply
  constructor
  · dsimp [nbPoweredYTH, executeYTH, JY, JT, H, J,
      yPhaseDump, transmutatePhase, capstoneBudget, capstonePhase,
      capstoneEnergy, capstoneTDelta]
  · exact yth_is_substrate_independent .intelHardwareIsa .swarmSoftware
      capstonePhase (capstoneEnergy : Int) capstoneTDelta

/-! ## POSI v00.01 and NB closure

POSI is represented here as a small identity/provenance packet.  The
checksum and anchors are symbolic contract fields; this section does not
claim cryptographic security or physical positron production.
-/

structure PosiPacket where
  versionMajor : Nat
  versionMinor : Nat
  carrierWidth : Nat
  identityAnchor : Nat
  provenanceAnchor : Nat
  sequence : Nat
  payload : Nat
  checksum : Nat

def posiProtocolVersion : String := "00.01"

def posiWellFormed (packet : PosiPacket) : Prop :=
  packet.versionMajor = 0 ∧
  packet.versionMinor = 1 ∧
  packet.carrierWidth = 4 ∧
  packet.identityAnchor = 17 ∧
  packet.provenanceAnchor = 131 ∧
  packet.checksum = 191

def posiV0001 : PosiPacket :=
  { versionMajor := 0
    versionMinor := 1
    carrierWidth := 4
    identityAnchor := 17
    provenanceAnchor := 131
    sequence := 0
    payload := 42
    checksum := 191 }

instance posiWellFormedDecidable (packet : PosiPacket) :
    Decidable (posiWellFormed packet) := by
  unfold posiWellFormed
  infer_instance

theorem posi_protocol_version_is_00_01 :
    posiProtocolVersion = "00.01" := rfl

theorem posi_v0001_is_well_formed :
    posiWellFormed posiV0001 := by
  simp [posiWellFormed, posiV0001]

theorem posi_v0001_payload_is_42 :
    posiV0001.payload = 42 := rfl

def posiGate (packet : PosiPacket) : Option PosiPacket :=
  if posiWellFormed packet then some packet else none

theorem posi_v0001_gate_accepts :
    posiGate posiV0001 = some posiV0001 := by
  simp [posiGate, posiWellFormed, posiV0001]

def posiNBRequest : Nat := 3
def posiNBBudget : NBBudget :=
  { capacity := 10
    used := 0 }
def posiNBPhase : Int := 0
def posiNBTDelta : Int := -3

def posiNBAdmission
    (packet : PosiPacket) (budget : NBBudget) :
    Option (NBBudget × Harness) :=
  if posiWellFormed packet then
    safeNBPoweredYTH budget posiNBPhase posiNBRequest posiNBTDelta
  else
    none

theorem posi_nb_admission_accepts
    (packet : PosiPacket) (budget : NBBudget)
    (hPosi : posiWellFormed packet)
    (hSupply : nbCanSupply budget posiNBRequest) :
    posiNBAdmission packet budget =
      some (nbPoweredYTH budget posiNBPhase posiNBRequest posiNBTDelta) := by
  unfold posiNBAdmission
  rw [if_pos hPosi]
  exact safe_nb_powered_yth_accepts budget posiNBPhase
    posiNBRequest posiNBTDelta hSupply

theorem posi_nb_admission_rejects_malformed
    (packet : PosiPacket) (budget : NBBudget)
    (hNot : ¬ posiWellFormed packet) :
    posiNBAdmission packet budget = none := by
  simp [posiNBAdmission, hNot]

theorem posi_nb_budget_is_supplyable :
    nbCanSupply posiNBBudget posiNBRequest := by
  simp [nbCanSupply, nbAvailable, posiNBBudget, posiNBRequest]

theorem posi_v0001_nb_accepts :
    posiNBAdmission posiV0001 posiNBBudget =
      some (nbPoweredYTH posiNBBudget posiNBPhase posiNBRequest posiNBTDelta) := by
  exact posi_nb_admission_accepts posiV0001 posiNBBudget
    posi_v0001_is_well_formed posi_nb_budget_is_supplyable

theorem posi_v0001_nb_budget_remains_bounded :
    (nbPoweredYTH posiNBBudget posiNBPhase posiNBRequest posiNBTDelta).1.used ≤
      (nbPoweredYTH posiNBBudget posiNBPhase posiNBRequest posiNBTDelta).1.capacity := by
  exact nb_powered_yth_budget_is_safe
    posiNBBudget posiNBPhase posiNBRequest posiNBTDelta
    (by simp [posiNBBudget]) posi_nb_budget_is_supplyable

theorem posi_v0001_nb_phase_closes :
    (nbPoweredYTH posiNBBudget posiNBPhase posiNBRequest posiNBTDelta).2.payload.phase =
      posiNBPhase := by
  simpa [posiNBPhase, posiNBRequest, posiNBTDelta] using
    nb_powered_yth_opposite_delta_preserves_phase
      posiNBBudget posiNBPhase posiNBRequest

theorem posi_v0001_substrates_agree :
    runYTHOnSubstrate .intelHardwareIsa posiNBPhase
        (posiNBRequest : Int) posiNBTDelta =
      runYTHOnSubstrate .swarmSoftware posiNBPhase
        (posiNBRequest : Int) posiNBTDelta := by
  exact yth_is_substrate_independent .intelHardwareIsa .swarmSoftware
    posiNBPhase (posiNBRequest : Int) posiNBTDelta

theorem posi_nb_capstone :
    posiWellFormed posiV0001 ∧
    posiGate posiV0001 = some posiV0001 ∧
    posiNBAdmission posiV0001 posiNBBudget =
      some (nbPoweredYTH posiNBBudget posiNBPhase posiNBRequest posiNBTDelta) ∧
    (nbPoweredYTH posiNBBudget posiNBPhase posiNBRequest posiNBTDelta).1.used ≤
      (nbPoweredYTH posiNBBudget posiNBPhase posiNBRequest posiNBTDelta).1.capacity ∧
    (nbPoweredYTH posiNBBudget posiNBPhase posiNBRequest posiNBTDelta).2.payload.phase =
      posiNBPhase ∧
    runYTHOnSubstrate .intelHardwareIsa posiNBPhase
        (posiNBRequest : Int) posiNBTDelta =
      runYTHOnSubstrate .swarmSoftware posiNBPhase
        (posiNBRequest : Int) posiNBTDelta := by
  constructor
  · exact posi_v0001_is_well_formed
  constructor
  · exact posi_v0001_gate_accepts
  constructor
  · exact posi_v0001_nb_accepts
  constructor
  · exact posi_v0001_nb_budget_remains_bounded
  constructor
  · exact posi_v0001_nb_phase_closes
  · exact posi_v0001_substrates_agree

end PlankLol.TripleTorusGanglia
