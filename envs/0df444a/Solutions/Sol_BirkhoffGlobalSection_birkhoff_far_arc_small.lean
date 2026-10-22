-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_far_arc_small
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T10:25:42.90547+00:00
-- url     : https://prove2.me/submissions/6ea16a25-1121-4b4c-b3b7-eeed3a7d1cd9

import Definitions.Def_BirkhoffGlobalSection
import Definitions.Def_BirkhoffShootingCoordinates
import Theorems.Thm_BirkhoffGlobalSection_partial_derivative_eq_update_deriv
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_circle_hamiltonian_lower_bound
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_realizes_first_critical_value
import Theorems.Thm_BirkhoffGlobalSection_leftCollisionPoint_mem_leftEnergyComponent
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_disk_near_side_force_negative
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_disk_vertical_tidal_factor
import Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_position_one
import Theorems.Thm_BirkhoffGlobalSection_jacobi_critical_momentum
import Definitions.Def_BirkhoffShootingArcs
import Theorems.Thm_BirkhoffGlobalSection_left_component_position_radius_lt_one
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_near_quadrant_monotone
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_compact

open BirkhoffGlobalSection Set Filter Topology Function

/-- differentiability of the regularized Hamiltonian away from the second collision -/
lemma K_differentiableAt (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s) :
    DifferentiableAt ℝ (leviCivitaHamiltonian μ c) s := by
  have hN : Real.sqrt (secondCollisionDistanceSq s) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  unfold leviCivitaHamiltonian wNormSq zNormSq
  have hsq : DifferentiableAt ℝ (fun s : Phase => Real.sqrt (secondCollisionDistanceSq s)) s := by
    unfold secondCollisionDistanceSq at hD ⊢
    exact (by fun_prop : DifferentiableAt ℝ (fun s : Phase =>
      (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) s).sqrt hD.ne'
  fun_prop (disch := assumption)

lemma K_line0 (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s) :
    HasDerivAt (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 0 t))
      (2 * c * s 0 + 4 * s 0 * (s 0 * s 3 - s 1 * s 2) + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 3
        - μ * s 3 - μ * (2 * s 0 / Real.sqrt (secondCollisionDistanceSq s)
          - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 0 * (2 * (s 0 ^ 2 + s 1 ^ 2) - 1) /
            Real.sqrt (secondCollisionDistanceSq s) ^ 3)) (s 0) := by
  have e : (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 0 t)) =
      fun t => (s 2 ^ 2 + s 3 ^ 2) / 2 + c * (t ^ 2 + s 1 ^ 2) - (1 - μ) / 2
        + 2 * (t ^ 2 + s 1 ^ 2) * (t * s 3 - s 1 * s 2) - μ * (t * s 3 + s 1 * s 2)
        - μ * (t ^ 2 + s 1 ^ 2) / Real.sqrt ((2 * (t ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * t * s 1) ^ 2) := by
    funext t
    simp [leviCivitaHamiltonian, wNormSq, zNormSq, secondCollisionDistanceSq, Function.update]
  rw [e]
  have hx := hasDerivAt_id' (s 0)
  have hin : HasDerivAt (fun t : ℝ => (2 * (t ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * t * s 1) ^ 2)
      (8 * s 0 * (2 * (s 0 ^ 2 + s 1 ^ 2) - 1)) (s 0) := by
    have := ((((hx.fun_pow 2).sub_const (s 1 ^ 2)).const_mul 2).sub_const 1).fun_pow 2
      |>.fun_add (((hx.const_mul 4).mul_const (s 1)).fun_pow 2)
    refine this.congr_deriv ?_
    simp; ring
  have hD' : (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2 ≠ 0 := hD.ne'
  have hS := hin.sqrt hD'
  have hNpos : 0 < Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) :=
    Real.sqrt_pos.2 hD
  have hsq := Real.sq_sqrt hD.le
  have hP := (hx.fun_pow 2).add_const (s 1 ^ 2)
  have htot := (((((hP.const_mul c).const_add ((s 2 ^ 2 + s 3 ^ 2) / 2)).sub_const ((1 - μ) / 2)).fun_add
    ((hP.const_mul 2).fun_mul ((hx.mul_const (s 3)).sub_const (s 1 * s 2)))).fun_sub
    ((hx.mul_const (s 3)).add_const (s 1 * s 2) |>.const_mul μ)).fun_sub
    ((hP.const_mul μ).fun_div hS hNpos.ne')
  refine htot.congr_deriv ?_
  unfold secondCollisionDistanceSq at hsq ⊢
  generalize Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) = N at *
  have hNne : N ≠ 0 := hNpos.ne'
  field_simp
  ring

lemma K_line1 (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s) :
    HasDerivAt (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 1 t))
      (2 * c * s 1 + 4 * s 1 * (s 0 * s 3 - s 1 * s 2) - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 2
        - μ * s 2 - μ * (2 * s 1 / Real.sqrt (secondCollisionDistanceSq s)
          - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 1 * (2 * (s 0 ^ 2 + s 1 ^ 2) + 1) /
            Real.sqrt (secondCollisionDistanceSq s) ^ 3)) (s 1) := by
  have e : (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 1 t)) =
      fun t => (s 2 ^ 2 + s 3 ^ 2) / 2 + c * (s 0 ^ 2 + t ^ 2) - (1 - μ) / 2
        + 2 * (s 0 ^ 2 + t ^ 2) * (s 0 * s 3 - t * s 2) - μ * (s 0 * s 3 + t * s 2)
        - μ * (s 0 ^ 2 + t ^ 2) / Real.sqrt ((2 * (s 0 ^ 2 - t ^ 2) - 1) ^ 2 + (4 * s 0 * t) ^ 2) := by
    funext t
    simp [leviCivitaHamiltonian, wNormSq, zNormSq, secondCollisionDistanceSq, Function.update]
  rw [e]
  have hx := hasDerivAt_id' (s 1)
  have hin : HasDerivAt (fun t : ℝ => (2 * (s 0 ^ 2 - t ^ 2) - 1) ^ 2 + (4 * s 0 * t) ^ 2)
      (8 * s 1 * (2 * (s 0 ^ 2 + s 1 ^ 2) + 1)) (s 1) := by
    have := ((((hx.fun_pow 2).const_sub (s 0 ^ 2)).const_mul 2).sub_const 1).fun_pow 2
      |>.fun_add ((hx.const_mul (4 * s 0)).fun_pow 2)
    refine this.congr_deriv ?_
    simp; ring
  have hD' : (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2 ≠ 0 := hD.ne'
  have hS := hin.sqrt hD'
  have hNpos : 0 < Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) :=
    Real.sqrt_pos.2 hD
  have hsq := Real.sq_sqrt hD.le
  have hP := (hx.fun_pow 2).const_add (s 0 ^ 2)
  have htot := (((((hP.const_mul c).const_add ((s 2 ^ 2 + s 3 ^ 2) / 2)).sub_const ((1 - μ) / 2)).fun_add
    ((hP.const_mul 2).fun_mul ((hx.mul_const (s 2)).const_sub (s 0 * s 3)))).fun_sub
    ((hx.mul_const (s 2)).const_add (s 0 * s 3) |>.const_mul μ)).fun_sub
    ((hP.const_mul μ).fun_div hS hNpos.ne')
  refine htot.congr_deriv ?_
  unfold secondCollisionDistanceSq at hsq ⊢
  generalize Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) = N at *
  have hNne : N ≠ 0 := hNpos.ne'
  field_simp
  ring

lemma K_line2 (μ c : ℝ) (s : Phase) :
    HasDerivAt (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 2 t))
      (s 2 - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 1 - μ * s 1) (s 2) := by
  have e : (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 2 t)) =
      fun t => (t ^ 2 + s 3 ^ 2) / 2 + c * (s 0 ^ 2 + s 1 ^ 2) - (1 - μ) / 2
        + 2 * (s 0 ^ 2 + s 1 ^ 2) * (s 0 * s 3 - s 1 * t) - μ * (s 0 * s 3 + s 1 * t)
        - μ * (s 0 ^ 2 + s 1 ^ 2) / Real.sqrt (secondCollisionDistanceSq s) := by
    funext t
    simp [leviCivitaHamiltonian, wNormSq, zNormSq, secondCollisionDistanceSq, Function.update]
  rw [e]
  have hx := hasDerivAt_id' (s 2)
  have := ((((((hx.fun_pow 2).add_const (s 3 ^ 2)).div_const 2).add_const (c * (s 0 ^ 2 + s 1 ^ 2))).sub_const
    ((1 - μ) / 2)).fun_add (((hx.const_mul (s 1)).const_sub (s 0 * s 3)).const_mul
      (2 * (s 0 ^ 2 + s 1 ^ 2)))).fun_sub (((hx.const_mul (s 1)).const_add (s 0 * s 3)).const_mul μ)
    |>.sub_const (μ * (s 0 ^ 2 + s 1 ^ 2) / Real.sqrt (secondCollisionDistanceSq s))
  refine this.congr_deriv ?_
  simp; try ring

lemma K_line3 (μ c : ℝ) (s : Phase) :
    HasDerivAt (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 3 t))
      (s 3 + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 0 - μ * s 0) (s 3) := by
  have e : (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 3 t)) =
      fun t => (s 2 ^ 2 + t ^ 2) / 2 + c * (s 0 ^ 2 + s 1 ^ 2) - (1 - μ) / 2
        + 2 * (s 0 ^ 2 + s 1 ^ 2) * (s 0 * t - s 1 * s 2) - μ * (s 0 * t + s 1 * s 2)
        - μ * (s 0 ^ 2 + s 1 ^ 2) / Real.sqrt (secondCollisionDistanceSq s) := by
    funext t
    simp [leviCivitaHamiltonian, wNormSq, zNormSq, secondCollisionDistanceSq, Function.update]
  rw [e]
  have hx := hasDerivAt_id' (s 3)
  have := ((((((hx.fun_pow 2).const_add (s 2 ^ 2)).div_const 2).add_const (c * (s 0 ^ 2 + s 1 ^ 2))).sub_const
    ((1 - μ) / 2)).fun_add (((hx.const_mul (s 0)).sub_const (s 1 * s 2)).const_mul
      (2 * (s 0 ^ 2 + s 1 ^ 2)))).fun_sub (((hx.const_mul (s 0)).add_const (s 1 * s 2)).const_mul μ)
    |>.sub_const (μ * (s 0 ^ 2 + s 1 ^ 2) / Real.sqrt (secondCollisionDistanceSq s))
  refine this.congr_deriv ?_
  simp; try ring

/-- Explicit Hamiltonian vector field of the regularized Hamiltonian. -/
lemma K_hvf (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s) :
    hamiltonianVectorField (leviCivitaHamiltonian μ c) s =
      ![s 2 - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 1 - μ * s 1,
        s 3 + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 0 - μ * s 0,
        -(2 * c * s 0 + 4 * s 0 * (s 0 * s 3 - s 1 * s 2) + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 3
          - μ * s 3 - μ * (2 * s 0 / Real.sqrt (secondCollisionDistanceSq s)
            - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 0 * (2 * (s 0 ^ 2 + s 1 ^ 2) - 1) /
              Real.sqrt (secondCollisionDistanceSq s) ^ 3)),
        -(2 * c * s 1 + 4 * s 1 * (s 0 * s 3 - s 1 * s 2) - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 2
          - μ * s 2 - μ * (2 * s 1 / Real.sqrt (secondCollisionDistanceSq s)
            - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 1 * (2 * (s 0 ^ 2 + s 1 ^ 2) + 1) /
              Real.sqrt (secondCollisionDistanceSq s) ^ 3))] := by
  have hd := K_differentiableAt μ c s hD
  unfold hamiltonianVectorField
  rw [partial_derivative_eq_update_deriv _ _ _ hd, partial_derivative_eq_update_deriv _ _ _ hd,
    partial_derivative_eq_update_deriv _ _ _ hd, partial_derivative_eq_update_deriv _ _ _ hd,
    (K_line0 μ c s hD).deriv, (K_line1 μ c s hD).deriv, (K_line2 μ c s).deriv, (K_line3 μ c s).deriv]

lemma flow_line_hasDerivAt' (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase))
      (hamiltonianVectorField (leviCivitaHamiltonian μ c)
        ((φ t x : LeftEnergyState μ c) : Phase)) t := by
  have h0 : HasDerivAt (fun u : ℝ => ((φ u (φ t x) : LeftEnergyState μ c) : Phase))
      (hamiltonianVectorField (leviCivitaHamiltonian μ c)
        ((φ t x : LeftEnergyState μ c) : Phase)) (t - t) := by
    rw [sub_self]; exact hφ (φ t x)
  have h := HasDerivAt.comp_sub_const t t h0
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [← Flow.map_add]; congr 1; ring

lemma mem_locus' {μ c : ℝ} (x : LeftEnergyState μ c) : (x : Phase) ∈ regularEnergyLocus μ c :=
  connectedComponentIn_subset _ _ x.2

/-- coordinate derivatives along a flow line -/
lemma flow_coords (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ) :
    let s := ((φ t x : LeftEnergyState μ c) : Phase)
    let N := Real.sqrt (secondCollisionDistanceSq s)
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 0)
        (s 2 - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 1 - μ * s 1) t ∧
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 1)
        (s 3 + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 0 - μ * s 0) t ∧
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 2)
        (-(2 * c * s 0 + 4 * s 0 * (s 0 * s 3 - s 1 * s 2) + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 3
          - μ * s 3 - μ * (2 * s 0 / N
            - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 0 * (2 * (s 0 ^ 2 + s 1 ^ 2) - 1) / N ^ 3))) t ∧
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 3)
        (-(2 * c * s 1 + 4 * s 1 * (s 0 * s 3 - s 1 * s 2) - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 2
          - μ * s 2 - μ * (2 * s 1 / N
            - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 1 * (2 * (s 0 ^ 2 + s 1 ^ 2) + 1) / N ^ 3))) t := by
  intro s N
  have h := flow_line_hasDerivAt' μ c φ hφ x t
  rw [K_hvf μ c _ (mem_locus' (φ t x)).2] at h
  have hc := hasDerivAt_pi.1 h
  exact ⟨by simpa using hc 0, by simpa using hc 1, by simpa using hc 2, by simpa using hc 3⟩

/-- the horizontal relative position moves with the Jacobi horizontal velocity -/
lemma xrel_hasDerivAt (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ) :
    let s := ((φ t x : LeftEnergyState μ c) : Phase)
    HasDerivAt (fun u : ℝ => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0)
      (4 * (s 0 * s 2 - s 1 * s 3) - 16 * (s 0 ^ 2 + s 1 ^ 2) * s 0 * s 1) t := by
  intro s
  obtain ⟨h0, h1, -, -⟩ := flow_coords μ c φ hφ x t
  have e : (fun u : ℝ => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0) =
      fun u => 2 * (((φ u x : LeftEnergyState μ c) : Phase) 0 ^ 2 -
        ((φ u x : LeftEnergyState μ c) : Phase) 1 ^ 2) := by
    funext u; simp [relativePosition, leviCivitaPosition]
  rw [e]
  have := ((h0.fun_pow 2).fun_sub (h1.fun_pow 2)).const_mul 2
  refine this.congr_deriv ?_
  simp only [s]; ring

/-- the vertical relative position along the flow -/
noncomputable def Yd (μ : ℝ) (s : Phase) : ℝ :=
  4 * (s 1 * s 2 + s 0 * s 3) + 8 * (s 0 ^ 2 + s 1 ^ 2) * (s 0 ^ 2 - s 1 ^ 2) -
    4 * μ * (s 0 ^ 2 + s 1 ^ 2)

noncomputable def XRd (s : Phase) : ℝ :=
  4 * (s 0 * s 2 - s 1 * s 3) - 16 * (s 0 ^ 2 + s 1 ^ 2) * s 0 * s 1

noncomputable def Vx (s : Phase) : ℝ := (s 2 * s 0 - s 3 * s 1) / (s 0 ^ 2 + s 1 ^ 2) - 4 * s 0 * s 1

noncomputable def Vy (μ : ℝ) (s : Phase) : ℝ :=
  (s 2 * s 1 + s 3 * s 0) / (s 0 ^ 2 + s 1 ^ 2) + 2 * (s 0 ^ 2 - s 1 ^ 2) - μ

/-- the Jacobi potential force components at the physical position of a Levi-Civita state -/
noncomputable def Omx (μ : ℝ) (s : Phase) : ℝ :=
  (2 * (s 0 ^ 2 - s 1 ^ 2) - μ) -
    (1 - μ) * (2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ) /
      Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) ^ 3 -
    μ * (2 * (s 0 ^ 2 - s 1 ^ 2) - μ - 1 + μ) /
      Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ - 1 + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) ^ 3

noncomputable def Omy (μ : ℝ) (s : Phase) : ℝ :=
  4 * s 0 * s 1 -
    (1 - μ) * (4 * s 0 * s 1) /
      Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) ^ 3 -
    μ * (4 * s 0 * s 1) /
      Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ - 1 + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) ^ 3

lemma jv_eq (μ : ℝ) (s : Phase) :
    jacobiVelocity (leviCivitaToJacobi μ s) 0 = Vx s ∧
      jacobiVelocity (leviCivitaToJacobi μ s) 1 = Vy μ s := by
  constructor <;>
    simp [jacobiVelocity, leviCivitaToJacobi, leviCivitaPosition, leviCivitaMomentum, zNormSq, Vx, Vy] <;>
    ring

lemma relPos_eq (μ : ℝ) (s : Phase) :
    relativePosition μ s 0 = 2 * (s 0 ^ 2 - s 1 ^ 2) ∧ relativePosition μ s 1 = 4 * s 0 * s 1 := by
  simp [relativePosition, leviCivitaPosition]

lemma XRd_eq (s : Phase) (hP : s 0 ^ 2 + s 1 ^ 2 ≠ 0) :
    XRd s = 4 * (s 0 ^ 2 + s 1 ^ 2) * Vx s := by
  unfold XRd Vx; field_simp; ring

lemma Yd_eq (μ : ℝ) (s : Phase) (hP : s 0 ^ 2 + s 1 ^ 2 ≠ 0) :
    Yd μ s = 4 * (s 0 ^ 2 + s 1 ^ 2) * Vy μ s := by
  unfold Yd Vy; field_simp; ring

lemma y_hasDerivAt (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ) :
    HasDerivAt (fun u : ℝ => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 1)
      (Yd μ ((φ t x : LeftEnergyState μ c) : Phase)) t := by
  obtain ⟨h0, h1, -, -⟩ := flow_coords μ c φ hφ x t
  have e : (fun u : ℝ => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 1) =
      fun u => 4 * ((φ u x : LeftEnergyState μ c) : Phase) 0 *
        ((φ u x : LeftEnergyState μ c) : Phase) 1 := by
    funext u; simp [relativePosition, leviCivitaPosition]
  rw [e]
  have := (h0.const_mul 4).fun_mul h1
  refine this.congr_deriv ?_
  simp only [Yd]; ring

lemma xrel_hasDerivAt' (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ) :
    HasDerivAt (fun u : ℝ => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0)
      (XRd ((φ t x : LeftEnergyState μ c) : Phase)) t :=
  xrel_hasDerivAt μ c φ hφ x t

noncomputable def nearR (μ c r : ℝ) : ℝ :=
  (1 - μ) + r ^ 2 * ((2 * r ^ 2 - μ) ^ 2 + 2 * μ / |2 * r ^ 2 - 1| - 2 * c)

noncomputable def farR (μ c r : ℝ) : ℝ :=
  (1 - μ) + r ^ 2 * ((2 * r ^ 2 + μ) ^ 2 + 2 * μ / (1 + 2 * r ^ 2) - 2 * c)

lemma nearStart_eq (μ c r : ℝ) :
    nearShootingStart μ c r = ![r, 0, 0, Real.sqrt (nearR μ c r) - r * (2 * r ^ 2 - μ)] := rfl

lemma farStart_eq (μ c r : ℝ) :
    farShootingStart μ c r = ![0, r, r * (2 * r ^ 2 + μ) - Real.sqrt (farR μ c r), 0] := rfl

lemma nearStart_D (μ c r : ℝ) :
    secondCollisionDistanceSq (nearShootingStart μ c r) = (2 * r ^ 2 - 1) ^ 2 := by
  simp [secondCollisionDistanceSq, nearShootingStart]

lemma farStart_D (μ c r : ℝ) :
    secondCollisionDistanceSq (farShootingStart μ c r) = (2 * r ^ 2 + 1) ^ 2 := by
  simp [secondCollisionDistanceSq, farShootingStart]; ring

lemma nearStart_K (μ c r : ℝ) (hR : 0 ≤ nearR μ c r) :
    leviCivitaHamiltonian μ c (nearShootingStart μ c r) = 0 := by
  have hs := Real.sq_sqrt hR
  have hD : Real.sqrt (secondCollisionDistanceSq (nearShootingStart μ c r)) = |2 * r ^ 2 - 1| := by
    rw [nearStart_D]; exact Real.sqrt_sq_eq_abs _
  unfold leviCivitaHamiltonian
  rw [hD]
  simp only [nearStart_eq, wNormSq, zNormSq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  generalize Real.sqrt (nearR μ c r) = S at *
  unfold nearR at hs
  generalize Real.sqrt ((1 - μ) + r ^ 2 * ((2 * r ^ 2 - μ) ^ 2 + 2 * μ / |2 * r ^ 2 - 1| - 2 * c))
    = S at *
  linear_combination hs / 2

lemma farStart_K (μ c r : ℝ) (hR : 0 ≤ farR μ c r) :
    leviCivitaHamiltonian μ c (farShootingStart μ c r) = 0 := by
  have hs := Real.sq_sqrt hR
  have hD : Real.sqrt (secondCollisionDistanceSq (farShootingStart μ c r)) = 1 + 2 * r ^ 2 := by
    rw [farStart_D, show (2 * r ^ 2 + 1) = 1 + 2 * r ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  unfold leviCivitaHamiltonian
  rw [hD]
  simp only [farStart_eq, wNormSq, zNormSq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  generalize Real.sqrt (farR μ c r) = S at *
  unfold farR at hs
  generalize Real.sqrt ((1 - μ) + r ^ 2 * ((2 * r ^ 2 + μ) ^ 2 + 2 * μ / (1 + 2 * r ^ 2) - 2 * c))
    = S at *
  linear_combination hs / 2

lemma nearR_continuousAt (μ c r : ℝ) (hr : 2 * r ^ 2 ≠ 1) : ContinuousAt (nearR μ c) r := by
  have h : |2 * r ^ 2 - 1| ≠ 0 := abs_ne_zero.2 (sub_ne_zero.2 hr)
  unfold nearR
  fun_prop (disch := exact h)

lemma farR_continuous (μ c : ℝ) : Continuous (farR μ c) := by
  unfold farR
  have : ∀ r : ℝ, 1 + 2 * r ^ 2 ≠ 0 := fun r => by positivity
  fun_prop (disch := exact this _)

lemma nearStart_continuousAt (μ c r : ℝ) (hr : 2 * r ^ 2 ≠ 1) :
    ContinuousAt (nearShootingStart μ c) r := by
  have hR := nearR_continuousAt μ c r hr
  have e : nearShootingStart μ c = fun r =>
      ![r, 0, 0, Real.sqrt (nearR μ c r) - r * (2 * r ^ 2 - μ)] := rfl
  rw [e]
  apply continuousAt_pi.2
  intro i
  fin_cases i
  · exact continuousAt_id
  · exact continuousAt_const
  · exact continuousAt_const
  · exact (hR.sqrt).sub (by fun_prop)

lemma farStart_continuous (μ c : ℝ) : Continuous (farShootingStart μ c) := by
  have hR := farR_continuous μ c
  have e : farShootingStart μ c = fun r =>
      ![0, r, r * (2 * r ^ 2 + μ) - Real.sqrt (farR μ c r), 0] := rfl
  rw [e]
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const
  · exact continuous_id
  · exact (by fun_prop : Continuous fun r : ℝ => r * (2 * r ^ 2 + μ)).sub hR.sqrt
  · exact continuous_const

/-- positions of the component are within distance `1` of the primary -/
lemma comp_radius (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
    (s : Phase) (hs : s ∈ leftEnergyComponent μ c) :
    (2 * (s 0 ^ 2 - s 1 ^ 2)) ^ 2 + (4 * s 0 * s 1) ^ 2 < 1 := by
  obtain ⟨ρ, hρ, hb⟩ := left_component_position_radius_lt_one μ c hμ0 hμ1 hc
  have := hb s hs
  simp only [leviCivitaPosition, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at this
  have e : 2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ = 2 * (s 0 ^ 2 - s 1 ^ 2) := by ring
  rw [e] at this
  linarith

/-- a connected piece of the energy locus through a point of the component stays in it -/
lemma mem_comp_of_path (μ c : ℝ) (S : ℝ → Phase) (r₀ r : ℝ) (hS : ContinuousOn S (uIcc r₀ r))
    (hloc : ∀ r' ∈ uIcc r₀ r, S r' ∈ regularEnergyLocus μ c)
    (h₀ : S r₀ ∈ leftEnergyComponent μ c) : S r ∈ leftEnergyComponent μ c := by
  have hpre : IsPreconnected (S '' uIcc r₀ r) := isPreconnected_uIcc.image _ hS
  have hsub := hpre.subset_connectedComponentIn (mem_image_of_mem _ left_mem_uIcc)
    (by rintro _ ⟨r', hr', rfl⟩; exact hloc r' hr')
  have heq : connectedComponentIn (regularEnergyLocus μ c) (S r₀) = leftEnergyComponent μ c :=
    (connectedComponentIn_eq h₀).symm
  rw [heq] at hsub
  exact hsub (mem_image_of_mem _ right_mem_uIcc)



lemma cont_relPos0 (μ : ℝ) : Continuous (fun s : Phase => relativePosition μ s 0) := by
  have : (fun s : Phase => relativePosition μ s 0) = fun s => 2 * (s 0 ^ 2 - s 1 ^ 2) := by
    funext s; exact (relPos_eq μ s).1
  rw [this]; fun_prop

lemma cont_relPos1 (μ : ℝ) : Continuous (fun s : Phase => relativePosition μ s 1) := by
  have : (fun s : Phase => relativePosition μ s 1) = fun s => 4 * s 0 * s 1 := by
    funext s; exact (relPos_eq μ s).2
  rw [this]; fun_prop

lemma cont_XRd : Continuous XRd := by unfold XRd; fun_prop

lemma cont_Yd (μ : ℝ) : Continuous (Yd μ) := by unfold Yd; fun_prop

lemma cont_zNormSq : Continuous zNormSq := by unfold zNormSq; fun_prop

lemma cont_Vx (s : Phase) (hP : s 0 ^ 2 + s 1 ^ 2 ≠ 0) : ContinuousAt Vx s := by
  unfold Vx; fun_prop (disch := exact hP)

lemma cont_Vy (μ : ℝ) (s : Phase) (hP : s 0 ^ 2 + s 1 ^ 2 ≠ 0) : ContinuousAt (Vy μ) s := by
  unfold Vy; fun_prop (disch := exact hP)

lemma coords_eq (μ : ℝ) : shootingCoordinates μ = fun s : Phase =>
    (Vy μ s / Real.sqrt (Vx s ^ 2 + Vy μ s ^ 2), -(4 * s 0 * s 1)) := by
  funext s
  simp only [shootingCoordinates, (jv_eq μ s).1, (jv_eq μ s).2, (relPos_eq μ s).2]

lemma cont_coords (μ : ℝ) (s : Phase) (hP : s 0 ^ 2 + s 1 ^ 2 ≠ 0) (hv : Vx s ≠ 0) :
    ContinuousAt (shootingCoordinates μ) s := by
  rw [coords_eq]
  have hx := cont_Vx s hP
  have hy := cont_Vy μ s hP
  have hsq : Real.sqrt (Vx s ^ 2 + Vy μ s ^ 2) ≠ 0 := by
    apply (Real.sqrt_pos.2 _).ne'
    have : 0 < Vx s ^ 2 := by positivity
    positivity
  apply ContinuousAt.prodMk
  · exact hy.div ((hx.pow 2).add (hy.pow 2)).sqrt hsq
  · fun_prop

lemma hasDerivAt_comp_neg' {g : ℝ → ℝ} {g' x : ℝ} (h : HasDerivAt g g' (-x)) :
    HasDerivAt (fun s => g (-s)) (-g') x := by
  have := h.comp x (hasDerivAt_neg x)
  simpa [Function.comp_def] using this

/-- Along a far arc the horizontal relative position is strictly increasing. -/
lemma far_arc_mono (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (τ : ℝ)
    (h : IsFarShootingArc φ x τ) :
    StrictMonoOn
      (fun u : ℝ => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0) (Icc 0 τ) := by
  obtain ⟨hτ, hlow, -, -, hv⟩ := h
  have hxd : ∀ t, HasDerivAt (fun u => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0) _ t :=
    fun t => xrel_hasDerivAt μ c φ hφ x t
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun t _ => (hxd t).continuousAt.continuousWithinAt)
  intro t ht
  rw [interior_Icc] at ht
  rw [(hxd t).deriv]
  have hy := hlow t ht
  have hvt := hv t ⟨ht.1, ht.2.le⟩
  generalize ((φ t x : LeftEnergyState μ c) : Phase) = s at hy hvt ⊢
  simp only [relativePosition, leviCivitaPosition, Matrix.cons_val_one, Matrix.head_cons] at hy
  have h0 : s 0 ≠ 0 := by rintro h; rw [h] at hy; simp at hy
  have hP : 0 < s 0 ^ 2 + s 1 ^ 2 := by positivity
  simp only [jacobiVelocity, leviCivitaToJacobi, leviCivitaPosition, leviCivitaMomentum, zNormSq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at hvt
  have e : 4 * (s 0 * s 2 - s 1 * s 3) - 16 * (s 0 ^ 2 + s 1 ^ 2) * s 0 * s 1 =
      4 * (s 0 ^ 2 + s 1 ^ 2) *
        ((s 2 * s 0 - s 3 * s 1) / (s 0 ^ 2 + s 1 ^ 2) - 4 * s 0 * s 1) := by
    field_simp; ring
  rw [e]; positivity


noncomputable def Xa (μ : ℝ) (s : Phase) : ℝ := s 2 - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 1 - μ * s 1
noncomputable def Xb (μ : ℝ) (s : Phase) : ℝ := s 3 + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 0 - μ * s 0
noncomputable def Xp (μ c : ℝ) (s : Phase) : ℝ :=
  -(2 * c * s 0 + 4 * s 0 * (s 0 * s 3 - s 1 * s 2) + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 3
    - μ * s 3 - μ * (2 * s 0 / Real.sqrt (secondCollisionDistanceSq s)
      - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 0 * (2 * (s 0 ^ 2 + s 1 ^ 2) - 1) /
        Real.sqrt (secondCollisionDistanceSq s) ^ 3))
noncomputable def Xq (μ c : ℝ) (s : Phase) : ℝ :=
  -(2 * c * s 1 + 4 * s 1 * (s 0 * s 3 - s 1 * s 2) - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 2
    - μ * s 2 - μ * (2 * s 1 / Real.sqrt (secondCollisionDistanceSq s)
      - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 1 * (2 * (s 0 ^ 2 + s 1 ^ 2) + 1) /
        Real.sqrt (secondCollisionDistanceSq s) ^ 3))

lemma flow_coords' (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 0)
        (Xa μ ((φ t x : LeftEnergyState μ c) : Phase)) t ∧
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 1)
        (Xb μ ((φ t x : LeftEnergyState μ c) : Phase)) t ∧
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 2)
        (Xp μ c ((φ t x : LeftEnergyState μ c) : Phase)) t ∧
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 3)
        (Xq μ c ((φ t x : LeftEnergyState μ c) : Phase)) t :=
  flow_coords μ c φ hφ x t

lemma cont_Xa (μ : ℝ) : Continuous (Xa μ) := by unfold Xa; fun_prop
lemma cont_Xb (μ : ℝ) : Continuous (Xb μ) := by unfold Xb; fun_prop
lemma cont_Xp (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s) :
    ContinuousAt (Xp μ c) s := by
  have hN : Real.sqrt (secondCollisionDistanceSq s) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have hN3 : Real.sqrt (secondCollisionDistanceSq s) ^ 3 ≠ 0 := pow_ne_zero _ hN
  have hsq : ContinuousAt (fun s : Phase => Real.sqrt (secondCollisionDistanceSq s)) s := by
    unfold secondCollisionDistanceSq; fun_prop
  unfold Xp
  have h1 := (continuousAt_apply 0 s).const_mul 2 |>.div hsq hN
  have h2 := ((by fun_prop : ContinuousAt (fun s : Phase =>
    4 * (s 0 ^ 2 + s 1 ^ 2) * s 0 * (2 * (s 0 ^ 2 + s 1 ^ 2) - 1)) s)).div (hsq.pow 3) hN3
  have h0 : ContinuousAt (fun s : Phase => 2 * c * s 0 + 4 * s 0 * (s 0 * s 3 - s 1 * s 2) +
    2 * (s 0 ^ 2 + s 1 ^ 2) * s 3 - μ * s 3) s := by fun_prop
  exact (h0.sub ((h1.sub h2).const_mul μ)).neg
lemma cont_Xq (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s) :
    ContinuousAt (Xq μ c) s := by
  have hN : Real.sqrt (secondCollisionDistanceSq s) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have hN3 : Real.sqrt (secondCollisionDistanceSq s) ^ 3 ≠ 0 := pow_ne_zero _ hN
  have hsq : ContinuousAt (fun s : Phase => Real.sqrt (secondCollisionDistanceSq s)) s := by
    unfold secondCollisionDistanceSq; fun_prop
  unfold Xq
  have h1 := (continuousAt_apply 1 s).const_mul 2 |>.div hsq hN
  have h2 := ((by fun_prop : ContinuousAt (fun s : Phase =>
    4 * (s 0 ^ 2 + s 1 ^ 2) * s 1 * (2 * (s 0 ^ 2 + s 1 ^ 2) + 1)) s)).div (hsq.pow 3) hN3
  have h0 : ContinuousAt (fun s : Phase => 2 * c * s 1 + 4 * s 1 * (s 0 * s 3 - s 1 * s 2) -
    2 * (s 0 ^ 2 + s 1 ^ 2) * s 2 - μ * s 2) s := by fun_prop
  exact (h0.sub ((h1.sub h2).const_mul μ)).neg

/-- A uniform bound on the vector field over the compact component. -/
lemma vf_bound (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c) :
    ∃ M > 0, ∀ s ∈ leftEnergyComponent μ c,
      |Xa μ s| ≤ M ∧ |Xb μ s| ≤ M ∧ |Xp μ c s| ≤ M ∧ |Xq μ c s| ≤ M := by
  have hK := left_energy_component_compact μ c hμ0 hμ1 hc
  have hD : ∀ s ∈ leftEnergyComponent μ c, 0 < secondCollisionDistanceSq s := fun s hs =>
    (connectedComponentIn_subset _ _ hs).2
  obtain ⟨C1, h1⟩ := hK.exists_bound_of_continuousOn (cont_Xa μ).continuousOn
  obtain ⟨C2, h2⟩ := hK.exists_bound_of_continuousOn (cont_Xb μ).continuousOn
  obtain ⟨C3, h3⟩ := hK.exists_bound_of_continuousOn
    (fun s hs => (cont_Xp μ c s (hD s hs)).continuousWithinAt)
  obtain ⟨C4, h4⟩ := hK.exists_bound_of_continuousOn
    (fun s hs => (cont_Xq μ c s (hD s hs)).continuousWithinAt)
  refine ⟨max (max C1 C2) (max C3 C4) + 1, by
    have := le_trans (norm_nonneg _) (h1 _ (leftCollisionPoint_mem_leftEnergyComponent μ c hμ0 hμ1))
    positivity, fun s hs => ⟨?_, ?_, ?_, ?_⟩⟩
  · have := h1 s hs; rw [Real.norm_eq_abs] at this
    linarith [le_max_left C1 C2, le_max_left (max C1 C2) (max C3 C4)]
  · have := h2 s hs; rw [Real.norm_eq_abs] at this
    linarith [le_max_right C1 C2, le_max_left (max C1 C2) (max C3 C4)]
  · have := h3 s hs; rw [Real.norm_eq_abs] at this
    linarith [le_max_left C3 C4, le_max_right (max C1 C2) (max C3 C4)]
  · have := h4 s hs; rw [Real.norm_eq_abs] at this
    linarith [le_max_right C3 C4, le_max_right (max C1 C2) (max C3 C4)]

/-- scalar mean value bound on a symmetric interval -/
lemma mvt_bound (f f' : ℝ → ℝ) (C s t : ℝ) (ht : |t| ≤ s)
    (hd : ∀ u ∈ Icc (-s) s, HasDerivAt f (f' u) u) (hb : ∀ u ∈ Icc (-s) s, |f' u| ≤ C) :
    |f t - f 0| ≤ C * s := by
  have hs : 0 ≤ s := le_trans (abs_nonneg _) ht
  have htm : t ∈ Icc (-s) s := abs_le.1 ht
  have h0m : (0:ℝ) ∈ Icc (-s) s := ⟨by linarith, hs⟩
  have := (convex_Icc (-s) s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hd u hu).hasDerivWithinAt) (fun u hu => by rw [Real.norm_eq_abs]; exact hb u hu)
    h0m htm
  simp only [Real.norm_eq_abs, sub_zero] at this
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0 h0m)
  calc |f t - f 0| ≤ C * |t| := this
    _ ≤ C * s := mul_le_mul_of_nonneg_left ht hC

lemma P_lt_half (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
    (s : Phase) (hs : s ∈ leftEnergyComponent μ c) : s 0 ^ 2 + s 1 ^ 2 < 1 / 2 := by
  have := comp_radius μ c hμ0 hμ1 hc s hs
  have e : (2 * (s 0 ^ 2 - s 1 ^ 2)) ^ 2 + (4 * s 0 * s 1) ^ 2 = 4 * (s 0 ^ 2 + s 1 ^ 2) ^ 2 := by
    ring
  rw [e] at this
  nlinarith [sq_nonneg (s 0), sq_nonneg (s 1)]

/-- First and second order estimates of the Levi-Civita flow. -/
lemma flow_estimates (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (M : ℝ) (hM : ∀ s ∈ leftEnergyComponent μ c,
      |Xa μ s| ≤ M ∧ |Xb μ s| ≤ M ∧ |Xp μ c s| ≤ M ∧ |Xq μ c s| ≤ M)
    (x : LeftEnergyState μ c) (s t : ℝ) (ht : |t| ≤ s) :
    |((φ t x : LeftEnergyState μ c) : Phase) 0 - (x : Phase) 0| ≤ M * s ∧
    |((φ t x : LeftEnergyState μ c) : Phase) 1 - (x : Phase) 1| ≤ M * s ∧
    |((φ t x : LeftEnergyState μ c) : Phase) 2 - (x : Phase) 2| ≤ M * s ∧
    |((φ t x : LeftEnergyState μ c) : Phase) 3 - (x : Phase) 3| ≤ M * s ∧
    |((φ t x : LeftEnergyState μ c) : Phase) 0 - (x : Phase) 0 - (x : Phase) 2 * t| ≤
      (M * s + 2 * (|(x : Phase) 1| + M * s)) * s ∧
    |((φ t x : LeftEnergyState μ c) : Phase) 1 - (x : Phase) 1 - (x : Phase) 3 * t| ≤
      (M * s + 2 * (|(x : Phase) 0| + M * s)) * s := by
  set γ : ℝ → Phase := fun u => ((φ u x : LeftEnergyState μ c) : Phase) with hγ
  have hγ0 : γ 0 = (x : Phase) := by simp [hγ]
  have hd := fun u => flow_coords' μ c φ hφ x u
  have first : ∀ u, |u| ≤ s → |γ u 0 - (x : Phase) 0| ≤ M * s ∧ |γ u 1 - (x : Phase) 1| ≤ M * s ∧
      |γ u 2 - (x : Phase) 2| ≤ M * s ∧ |γ u 3 - (x : Phase) 3| ≤ M * s := by
    intro u hu
    rw [← hγ0]
    refine ⟨mvt_bound (fun u => γ u 0) _ M s u hu (fun v _ => (hd v).1)
        (fun v _ => (hM _ (φ v x).2).1),
      mvt_bound (fun u => γ u 1) _ M s u hu (fun v _ => (hd v).2.1)
        (fun v _ => (hM _ (φ v x).2).2.1),
      mvt_bound (fun u => γ u 2) _ M s u hu (fun v _ => (hd v).2.2.1)
        (fun v _ => (hM _ (φ v x).2).2.2.1),
      mvt_bound (fun u => γ u 3) _ M s u hu (fun v _ => (hd v).2.2.2)
        (fun v _ => (hM _ (φ v x).2).2.2.2)⟩
  obtain ⟨f0, f1, f2, f3⟩ := first t ht
  refine ⟨f0, f1, f2, f3, ?_, ?_⟩
  · have := mvt_bound (fun u => γ u 0 - (x : Phase) 0 - (x : Phase) 2 * u)
      (fun u => Xa μ (γ u) - (x : Phase) 2) _ s t ht
      (fun v _ => ((hd v).1.sub_const _).sub ((hasDerivAt_id v).const_mul _ |>.congr_deriv (by ring)))
      (fun v hv => by
        have hv' : |v| ≤ s := abs_le.2 hv
        obtain ⟨g0, g1, g2, g3⟩ := first v hv'
        have hP := P_lt_half μ c hμ0 hμ1 hc _ (φ v x).2
        have e : Xa μ (γ v) - (x : Phase) 2 = (γ v 2 - (x : Phase) 2) -
            (2 * (γ v 0 ^ 2 + γ v 1 ^ 2) + μ) * γ v 1 := by unfold Xa; ring
        rw [e]
        have hb1 : |γ v 1| ≤ |(x : Phase) 1| + M * s := by
          have := abs_sub_abs_le_abs_sub (γ v 1) ((x : Phase) 1); linarith
        have hk : |2 * (γ v 0 ^ 2 + γ v 1 ^ 2) + μ| ≤ 2 := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg (γ v 0), sq_nonneg (γ v 1)]
        calc |(γ v 2 - (x : Phase) 2) - (2 * (γ v 0 ^ 2 + γ v 1 ^ 2) + μ) * γ v 1|
            ≤ |γ v 2 - (x : Phase) 2| + |2 * (γ v 0 ^ 2 + γ v 1 ^ 2) + μ| * |γ v 1| := by
              rw [← abs_mul]; exact abs_sub _ _
          _ ≤ M * s + 2 * (|(x : Phase) 1| + M * s) := by
              gcongr)
    simp only [hγ0, mul_zero, sub_zero, sub_self] at this
    simpa [hγ] using this
  · have := mvt_bound (fun u => γ u 1 - (x : Phase) 1 - (x : Phase) 3 * u)
      (fun u => Xb μ (γ u) - (x : Phase) 3) _ s t ht
      (fun v _ => ((hd v).2.1.sub_const _).sub ((hasDerivAt_id v).const_mul _ |>.congr_deriv (by ring)))
      (fun v hv => by
        have hv' : |v| ≤ s := abs_le.2 hv
        obtain ⟨g0, g1, g2, g3⟩ := first v hv'
        have hP := P_lt_half μ c hμ0 hμ1 hc _ (φ v x).2
        have e : Xb μ (γ v) - (x : Phase) 3 = (γ v 3 - (x : Phase) 3) +
            (2 * (γ v 0 ^ 2 + γ v 1 ^ 2) - μ) * γ v 0 := by unfold Xb; ring
        rw [e]
        have hb0 : |γ v 0| ≤ |(x : Phase) 0| + M * s := by
          have := abs_sub_abs_le_abs_sub (γ v 0) ((x : Phase) 0); linarith
        have hk : |2 * (γ v 0 ^ 2 + γ v 1 ^ 2) - μ| ≤ 2 := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg (γ v 0), sq_nonneg (γ v 1)]
        calc |(γ v 3 - (x : Phase) 3) + (2 * (γ v 0 ^ 2 + γ v 1 ^ 2) - μ) * γ v 0|
            ≤ |γ v 3 - (x : Phase) 3| + |2 * (γ v 0 ^ 2 + γ v 1 ^ 2) - μ| * |γ v 0| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ M * s + 2 * (|(x : Phase) 0| + M * s) := by
              gcongr)
    simp only [hγ0, mul_zero, sub_zero, sub_self] at this
    simpa [hγ] using this



/-- The collision circle lies on the selected component. -/
lemma collision_circle_mem (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (θ : ℝ) :
    (![0, 0, Real.sqrt (1 - μ) * Real.cos θ, Real.sqrt (1 - μ) * Real.sin θ] : Phase) ∈
      leftEnergyComponent μ c := by
  have h0 : (![0, 0, Real.sqrt (1 - μ) * Real.cos 0, Real.sqrt (1 - μ) * Real.sin 0] : Phase) =
      leftCollisionPoint μ := by
    funext i; fin_cases i <;> simp [leftCollisionPoint]
  apply mem_comp_of_path μ c (fun θ => (![0, 0, Real.sqrt (1 - μ) * Real.cos θ,
    Real.sqrt (1 - μ) * Real.sin θ] : Phase)) 0 θ
  · apply Continuous.continuousOn
    apply continuous_pi; intro i; fin_cases i <;> simp <;> fun_prop
  · intro θ' _
    refine ⟨?_, ?_⟩
    · have hs := Real.sq_sqrt (show (0:ℝ) ≤ 1 - μ by linarith)
      simp [leviCivitaHamiltonian, wNormSq, zNormSq, secondCollisionDistanceSq]
      nlinarith [Real.sin_sq_add_cos_sq θ']
    · simp [secondCollisionDistanceSq]
  · convert leftCollisionPoint_mem_leftEnergyComponent μ c hμ0 hμ1 using 1

lemma nearR_zero (μ c : ℝ) : nearR μ c 0 = 1 - μ := by simp [nearR]
lemma farR_zero (μ c : ℝ) : farR μ c 0 = 1 - μ := by simp [farR]

lemma nearStart_zero_mem (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    nearShootingStart μ c 0 ∈ leftEnergyComponent μ c := by
  have := collision_circle_mem μ c hμ0 hμ1 (Real.pi / 2)
  have e : nearShootingStart μ c 0 = ![0, 0, Real.sqrt (1 - μ) * Real.cos (Real.pi / 2),
      Real.sqrt (1 - μ) * Real.sin (Real.pi / 2)] := by
    rw [nearStart_eq, nearR_zero]; funext i; fin_cases i <;> simp
  rwa [e]

lemma farStart_zero_mem (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    farShootingStart μ c 0 ∈ leftEnergyComponent μ c := by
  have := collision_circle_mem μ c hμ0 hμ1 Real.pi
  have e : farShootingStart μ c 0 = ![0, 0, Real.sqrt (1 - μ) * Real.cos Real.pi,
      Real.sqrt (1 - μ) * Real.sin Real.pi] := by
    rw [farStart_eq, farR_zero]; funext i; fin_cases i <;> simp
  rwa [e]

lemma evt_lt {f : ℝ → ℝ} (hf : ContinuousAt f 0) {b : ℝ} (h : f 0 < b) :
    ∀ᶠ r in 𝓝 (0:ℝ), f r < b := hf.eventually (Iio_mem_nhds h)

lemma evt_gt {f : ℝ → ℝ} (hf : ContinuousAt f 0) {b : ℝ} (h : b < f 0) :
    ∀ᶠ r in 𝓝 (0:ℝ), b < f r := hf.eventually (Ioi_mem_nhds h)

noncomputable def Gfar (μ α p q : ℝ) : ℝ :=
  (p - q - 2 * α * μ) / Real.sqrt ((8 * α ^ 3 - p - q) ^ 2 + (p - q - 2 * α * μ) ^ 2)

lemma coords_far_cross (μ : ℝ) (s : Phase) (α : ℝ) (hα : 0 < α) (h0 : s 0 = -α) (h1 : s 1 = α) :
    shootingCoordinates μ s = (Gfar μ α (s 2) (s 3), 4 * α ^ 2) := by
  rw [coords_eq]
  simp only [Vx, Vy, Gfar, h0, h1]
  congr 1
  · have e1 : (s 2 * -α - s 3 * α) / ((-α) ^ 2 + α ^ 2) - 4 * -α * α =
        (8 * α ^ 3 - s 2 - s 3) / (2 * α) := by field_simp; ring
    have e2 : (s 2 * α + s 3 * -α) / ((-α) ^ 2 + α ^ 2) + 2 * ((-α) ^ 2 - α ^ 2) - μ =
        (s 2 - s 3 - 2 * α * μ) / (2 * α) := by field_simp; ring
    rw [e1, e2, div_pow, div_pow, ← add_div, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by positivity), div_div_div_cancel_right₀ (by positivity)]
  · ring

lemma Gfar_limit (μ : ℝ) (hμ1 : μ < 1) :
    Tendsto (fun q : ℝ × ℝ × ℝ => Gfar μ q.1 q.2.1 q.2.2) (𝓝 (0, -Real.sqrt (1 - μ), 0))
      (𝓝 (-(Real.sqrt 2 / 2))) := by
  have hv : 0 < Real.sqrt (1 - μ) := Real.sqrt_pos.2 (by linarith)
  have hden : Real.sqrt ((8 * 0 ^ 3 - -Real.sqrt (1 - μ) - 0) ^ 2 +
      (-Real.sqrt (1 - μ) - 0 - 2 * 0 * μ) ^ 2) ≠ 0 := by
    apply (Real.sqrt_pos.2 _).ne'; simp; positivity
  have hc : ContinuousAt (fun q : ℝ × ℝ × ℝ => Gfar μ q.1 q.2.1 q.2.2)
      (0, -Real.sqrt (1 - μ), 0) := by
    unfold Gfar
    exact ContinuousAt.div (by fun_prop)
      ((by fun_prop : ContinuousAt (fun q : ℝ × ℝ × ℝ => (8 * q.1 ^ 3 - q.2.1 - q.2.2) ^ 2 +
        (q.2.1 - q.2.2 - 2 * q.1 * μ) ^ 2) _).sqrt) hden
  have hval : Gfar μ 0 (-Real.sqrt (1 - μ)) 0 = -(Real.sqrt 2 / 2) := by
    have e : Gfar μ 0 (-Real.sqrt (1 - μ)) 0 = -(Real.sqrt (1 - μ) /
        Real.sqrt (Real.sqrt (1 - μ) ^ 2 + Real.sqrt (1 - μ) ^ 2)) := by
      unfold Gfar; rw [← neg_div]; congr 1 <;> ring_nf
    rw [e]
    have hv2 : Real.sqrt (1 - μ) ^ 2 + Real.sqrt (1 - μ) ^ 2 = (Real.sqrt 2 * Real.sqrt (1 - μ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring
    rw [hv2, Real.sqrt_sq (by positivity)]
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    congr 1
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have := hc.tendsto
  simp only at this
  rwa [hval] at this

lemma vx_pos_aux (a b p q u v r M S : ℝ) (hu : 0 < u) (huS : u ≤ S) (hM0 : 0 < M) (hS : 0 < S)
    (hA1 : a ≤ -(u * (v - 3 * M * u - 2 * r))) (hA2 : 0 < v - 3 * M * u - 2 * r)
    (hB1 : 0 < b) (hB2 : b ≤ r + 3 * M * S ^ 2) (hr : 0 ≤ r) (e2 : |p + v| ≤ M * u) (e3 : |q| ≤ M * u)
    (H2 : 3 * M * S + 2 * r < v)
    (H5 : M * (r + 3 * M * S ^ 2) < (v - M * S) * (v - 3 * M * S - 2 * r)) :
    0 < (p * a - q * b) / (a ^ 2 + b ^ 2) - 4 * a * b := by
  have hMu : M * u ≤ M * S := mul_le_mul_of_nonneg_left huS hM0.le
  have hMS : 0 < M * S := mul_pos hM0 hS
  have hupos := mul_pos hu hA2
  have hA0 : a < 0 := by linarith
  have hP : 0 < a ^ 2 + b ^ 2 := by
    have : 0 < a ^ 2 := even_two.pow_pos hA0.ne
    have : 0 ≤ b ^ 2 := sq_nonneg b
    linarith
  have hvu : 0 < v - M * u := by linarith
  have e2' := abs_le.1 e2
  have hpa : (v - M * u) * (u * (v - 3 * M * u - 2 * r)) ≤ p * a := by
    have h1 : v - M * u ≤ -p := by linarith [e2'.2]
    have h2 : u * (v - 3 * M * u - 2 * r) ≤ -a := by linarith
    have := mul_le_mul h1 h2 hupos.le (by linarith)
    linarith
  have hqb : |q * b| ≤ M * u * (r + 3 * M * S ^ 2) := by
    rw [abs_mul, abs_of_pos hB1]
    exact mul_le_mul e3 hB2 hB1.le (by positivity)
  have hH : M * (r + 3 * M * S ^ 2) < (v - M * u) * (v - 3 * M * u - 2 * r) := by
    have h1 : v - M * S ≤ v - M * u := by linarith
    have h2 : v - 3 * M * S - 2 * r ≤ v - 3 * M * u - 2 * r := by linarith
    have h3 : 0 < v - 3 * M * S - 2 * r := by linarith
    have := mul_le_mul h1 h2 h3.le (by linarith)
    linarith
  have hlt : u * (M * (r + 3 * M * S ^ 2)) < u * ((v - M * u) * (v - 3 * M * u - 2 * r)) :=
    mul_lt_mul_of_pos_left hH hu
  have hqb' := abs_le.1 hqb
  have hkey : 0 < p * a - q * b := by
    have e1 : M * u * (r + 3 * M * S ^ 2) = u * (M * (r + 3 * M * S ^ 2)) := by ring
    have e2 : (v - M * u) * (u * (v - 3 * M * u - 2 * r)) =
        u * ((v - M * u) * (v - 3 * M * u - 2 * r)) := by ring
    linarith [hqb'.2]
  have : 0 < -(4 * a * b) := by
    have := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num : (0:ℝ) < 4) hA0) hB1
    linarith
  have : 0 < (p * a - q * b) / (a ^ 2 + b ^ 2) := div_pos hkey hP
  linarith

set_option maxHeartbeats 2000000 in
/-- Quantitative far arc for a start close to the primary. -/
lemma core_far (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (M : ℝ) (hM : ∀ s ∈ leftEnergyComponent μ c,
      |Xa μ s| ≤ M ∧ |Xb μ s| ≤ M ∧ |Xp μ c s| ≤ M ∧ |Xq μ c s| ≤ M) (hM0 : 0 < M)
    (x : LeftEnergyState μ c) (r v S : ℝ)
    (hx0 : (x : Phase) 0 = 0) (hx1 : (x : Phase) 1 = r) (hx2 : (x : Phase) 2 = -v)
    (hx3 : (x : Phase) 3 = 0) (hr : 0 < r) (hS : 0 < S)
    (hvS : 2 * r ≤ v * S) (H1 : 3 * M * S ^ 2 < r) (H2 : 3 * M * S + 2 * r < v)
    (H3 : 6 * M * S ^ 2 + 2 * r * S < r)
    (H4 : 0 < v - 2 * M * S - 2 * (v * S + 3 * M * S ^ 2 + 2 * r * S) - 2 * (r + 3 * M * S ^ 2))
    (H5 : M * (r + 3 * M * S ^ 2) < (v - M * S) * (v - 3 * M * S - 2 * r)) :
    ∃ τ, 0 < τ ∧ τ < S ∧ IsFarShootingArc φ x τ ∧ (∀ τ', IsFarShootingArc φ x τ' → τ' = τ) ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 0 = -((φ τ x : LeftEnergyState μ c) : Phase) 1 ∧
      0 < ((φ τ x : LeftEnergyState μ c) : Phase) 1 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 1 ≤ r + 3 * M * S ^ 2 ∧
      |((φ τ x : LeftEnergyState μ c) : Phase) 2 + v| ≤ M * S ∧
      |((φ τ x : LeftEnergyState μ c) : Phase) 3| ≤ M * S := by
  set γ : ℝ → Phase := fun u => ((φ u x : LeftEnergyState μ c) : Phase) with hγ
  have hγ0 : γ 0 = (x : Phase) := by simp [hγ]
  have hv : 0 < v := by nlinarith
  have est : ∀ u ∈ Icc 0 S, |γ u 0 + v * u| ≤ (3 * M * u + 2 * r) * u ∧ |γ u 1 - r| ≤ 3 * M * u ^ 2 ∧
      |γ u 2 + v| ≤ M * u ∧ |γ u 3| ≤ M * u := by
    intro u hu
    obtain ⟨-, -, e2, e3, e4, e5⟩ := flow_estimates μ c hμ0 hμ1 hc φ hφ M hM x u u
      (by rw [abs_of_nonneg hu.1])
    rw [hx0, hx1, hx2, hx3] at *
    simp only [hγ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : |((φ u x : LeftEnergyState μ c) : Phase) 0 - 0 - -v * u| =
          |((φ u x : LeftEnergyState μ c) : Phase) 0 + v * u| := by ring_nf
      rw [this, abs_of_pos hr] at e4; nlinarith
    · have : |((φ u x : LeftEnergyState μ c) : Phase) 1 - r - 0 * u| =
          |((φ u x : LeftEnergyState μ c) : Phase) 1 - r| := by ring_nf
      rw [this] at e5; simp only [abs_zero] at e5; nlinarith
    · simpa using e2
    · simpa using e3
  have hb : ∀ u ∈ Icc 0 S, 0 < γ u 1 ∧ γ u 1 ≤ r + 3 * M * S ^ 2 := by
    intro u hu
    have h := abs_le.1 (est u hu).2.1
    have : 3 * M * u ^ 2 ≤ 3 * M * S ^ 2 := by
      have := pow_le_pow_left₀ hu.1 hu.2 2; nlinarith
    constructor <;> linarith [h.1, h.2]
  have ha : ∀ u ∈ Ioc 0 S, γ u 0 ≤ -(u * (v - 3 * M * u - 2 * r)) ∧ 0 < v - 3 * M * u - 2 * r := by
    intro u hu
    have h := abs_le.1 (est u ⟨hu.1.le, hu.2⟩).1
    have : 3 * M * u + 2 * r < v := by nlinarith [hu.2]
    constructor
    · nlinarith
    · linarith
  have haabs : ∀ u ∈ Icc 0 S, |γ u 0| ≤ v * S + 3 * M * S ^ 2 + 2 * r * S := by
    intro u hu
    have h := abs_le.1 (est u hu).1
    have h1 : (3 * M * u + 2 * r) * u ≤ 3 * M * S ^ 2 + 2 * r * S := by
      have hu2 : u ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
      nlinarith [hu.1, hu.2]
    have h2 : v * u ≤ v * S := mul_le_mul_of_nonneg_left hu.2 hv.le
    have h3 : 0 ≤ v * u := mul_nonneg hv.le hu.1
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  set g : ℝ → ℝ := fun u => γ u 0 + γ u 1 with hg
  have hgd : ∀ u, HasDerivAt g (Xa μ (γ u) + Xb μ (γ u)) u := fun u =>
    (flow_coords' μ c φ hφ x u).1.add (flow_coords' μ c φ hφ x u).2.1
  have hganti : StrictAntiOn g (Icc 0 S) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun u _ => (hgd u).continuousAt.continuousWithinAt)
    intro u hu
    rw [interior_Icc] at hu
    rw [(hgd u).deriv]
    have hu' : u ∈ Icc 0 S := Ioo_subset_Icc_self hu
    obtain ⟨-, -, e2, e3⟩ := est u hu'
    have hP := P_lt_half μ c hμ0 hμ1 hc _ (φ u x).2
    have hB := hb u hu'
    have hA := haabs u hu'
    have e2' := abs_le.1 e2
    have e3' := abs_le.1 e3
    have hMu : M * u ≤ M * S := mul_le_mul_of_nonneg_left hu.2.le hM0.le
    set a := γ u 0; set b := γ u 1
    have hk1 : |(2 * (a ^ 2 + b ^ 2) + μ) * b| ≤ 2 * (r + 3 * M * S ^ 2) := by
      rw [abs_mul, abs_of_pos hB.1]
      have : |2 * (a ^ 2 + b ^ 2) + μ| ≤ 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
      calc |2 * (a ^ 2 + b ^ 2) + μ| * b ≤ 2 * b := mul_le_mul_of_nonneg_right this hB.1.le
        _ ≤ _ := by linarith [hB.2]
    have hk2 : |(2 * (a ^ 2 + b ^ 2) - μ) * a| ≤ 2 * (v * S + 3 * M * S ^ 2 + 2 * r * S) := by
      rw [abs_mul]
      have : |2 * (a ^ 2 + b ^ 2) - μ| ≤ 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
      calc |2 * (a ^ 2 + b ^ 2) - μ| * |a| ≤ 2 * |a| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ ≤ _ := by linarith
    have e : Xa μ (γ u) + Xb μ (γ u) = γ u 2 + γ u 3 -
        (2 * (a ^ 2 + b ^ 2) + μ) * b + (2 * (a ^ 2 + b ^ 2) - μ) * a := by
      simp only [Xa, Xb, a, b]; ring
    rw [e]
    have := abs_le.1 hk1; have := abs_le.1 hk2
    linarith
  have hg0 : g 0 = r := by simp [hg, hγ0, hx0, hx1]
  have hgS : g S < 0 := by
    have h1 := abs_le.1 (est S ⟨hS.le, le_refl _⟩).1
    have h2 := abs_le.1 (est S ⟨hS.le, le_refl _⟩).2.1
    have e1 : (3 * M * S + 2 * r) * S = 3 * M * S ^ 2 + 2 * r * S := by ring
    simp only [hg]
    linarith [h1.2, h2.2]
  obtain ⟨τ, hτ, hgτ⟩ := intermediate_value_Ioo' hS.le
    (fun u _ => (hgd u).continuousAt.continuousWithinAt) ⟨hgS, by rw [hg0]; exact hr⟩
  have hgpos : ∀ u ∈ Ico 0 τ, 0 < g u := by
    intro u hu
    rw [← hgτ]
    exact hganti ⟨hu.1, by linarith [hu.2, hτ.2]⟩ ⟨hτ.1.le, hτ.2.le⟩ hu.2
  have hxrel : ∀ u, relativePosition μ (γ u) 0 = 2 * (γ u 0 - γ u 1) * g u := by
    intro u; rw [(relPos_eq μ _).1]; simp only [hg]; ring
  have hyrel : ∀ u, relativePosition μ (γ u) 1 = 4 * γ u 0 * γ u 1 := fun u => (relPos_eq μ _).2
  have hyneg : ∀ u ∈ Ioc 0 S, relativePosition μ (γ u) 1 < 0 := by
    intro u hu
    rw [hyrel]
    have hA := ha u hu
    have hB := hb u ⟨hu.1.le, hu.2⟩
    have : γ u 0 < 0 := by have := mul_pos hu.1 hA.2; linarith [hA.1]
    have := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num : (0:ℝ) < 4) this) hB.1
    linarith
  have hvx : ∀ u ∈ Ioc 0 S, 0 < Vx (γ u) := by
    intro u hu
    have hA := ha u hu
    have hB := hb u ⟨hu.1.le, hu.2⟩
    obtain ⟨-, -, e2, e3⟩ := est u ⟨hu.1.le, hu.2⟩
    unfold Vx
    exact vx_pos_aux _ _ _ _ u v r M S hu.1 hu.2 hM0 hS hA.1 hA.2 hB.1 hB.2 hr.le e2 e3 H2 H5
  have hx0τ : relativePosition μ (γ τ) 0 = 0 := by rw [hxrel τ, hgτ, mul_zero]
  have harc : IsFarShootingArc φ x τ := by
    simp only [hγ] at hyneg hvx hx0τ
    refine ⟨hτ.1, fun u hu => hyneg u ⟨hu.1, by linarith [hu.2, hτ.2]⟩,
      hyneg τ ⟨hτ.1, hτ.2.le⟩, hx0τ, fun u hu => ?_⟩
    rw [(jv_eq μ _).1]
    have hu' : u ∈ Ioc 0 S := ⟨hu.1, lt_of_le_of_lt hu.2 hτ.2 |>.le⟩
    exact hvx u hu'
  refine ⟨τ, hτ.1, hτ.2, harc, ?_, ?_, (hb τ ⟨hτ.1.le, hτ.2.le⟩).1,
    (hb τ ⟨hτ.1.le, hτ.2.le⟩).2, ?_, ?_⟩
  · intro τ' h'
    have hmono := far_arc_mono μ c φ hφ x τ' h'
    rcases lt_trichotomy τ' τ with hl | he | hl
    · exfalso
      have h1 := h'.2.2.2.1
      have e := hxrel τ'
      simp only [hγ] at e
      rw [e] at h1
      have hA := ha τ' ⟨h'.1, by linarith [hτ.2]⟩
      have hB := hb τ' ⟨h'.1.le, by linarith [hτ.2]⟩
      have hG := hgpos τ' ⟨h'.1.le, hl⟩
      have hA0 : γ τ' 0 < 0 := by have := mul_pos h'.1 hA.2; linarith [hA.1]
      have : 2 * (γ τ' 0 - γ τ' 1) * g τ' < 0 := by
        have : 2 * (γ τ' 0 - γ τ' 1) < 0 := by linarith [hB.1]
        exact mul_neg_of_neg_of_pos this hG
      simp only [hγ] at this
      linarith
    · exact he
    · exfalso
      have := hmono ⟨hτ.1.le, hl.le⟩ ⟨h'.1.le, le_refl _⟩ hl
      simp only at this
      rw [h'.2.2.2.1] at this
      have e := hxrel τ
      simp only [hγ] at e
      rw [e, hgτ, mul_zero] at this
      exact lt_irrefl _ this
  · have : g τ = 0 := hgτ
    simp only [hg, hγ] at this
    linarith
  · have := (est τ ⟨hτ.1.le, hτ.2.le⟩).2.2.1
    exact le_trans this (mul_le_mul_of_nonneg_left hτ.2.le hM0.le)
  · have := (est τ ⟨hτ.1.le, hτ.2.le⟩).2.2.2
    exact le_trans this (mul_le_mul_of_nonneg_left hτ.2.le hM0.le)



theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ ε > 0, (∀ r ∈ Set.Ioo 0 ε, ∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c r ∧
        ∃ τ : ℝ, IsFarShootingArc φ x τ) ∧
      ∀ η > 0, ∃ δ > 0, ∀ r ∈ Set.Ioo 0 δ, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
        (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ →
          dist (shootingCoordinates μ ((φ τ x : LeftEnergyState μ c) : Phase))
            (-(Real.sqrt 2 / 2), 0) < η := by
  obtain ⟨M, hM0, hM⟩ := vf_bound μ c hμ0 hμ1 hc
  set v₀ := Real.sqrt (1 - μ) with hv₀
  have hv₀0 : 0 < v₀ := Real.sqrt_pos.2 (by linarith)
  set v : ℝ → ℝ := fun r => Real.sqrt (farR μ c r) - r * (2 * r ^ 2 + μ) with hvdef
  have hv0 : v 0 = v₀ := by simp [hvdef, farR_zero, hv₀]
  have hvc : ContinuousAt v 0 :=
    (((farR_continuous μ c).continuousAt).sqrt).sub (by fun_prop)
  have hRc : ContinuousAt (farR μ c) 0 := (farR_continuous μ c).continuousAt
  set S : ℝ → ℝ := fun r => 4 * r / v₀ with hSdef
  have hSc : Continuous S := by simp only [hSdef]; fun_prop
  -- the smallness conditions
  have Ecore : ∀ᶠ r in 𝓝 (0:ℝ), v₀ / 2 < v r ∧ v r < 2 * v₀ ∧ 0 < farR μ c r ∧ 2 * r ^ 2 < 1 ∧
      48 * M * r / v₀ ^ 2 < 1 ∧ 12 * M * r / v₀ + 2 * r < v₀ / 2 ∧
      96 * M * r / v₀ ^ 2 + 8 * r / v₀ < 1 ∧
      0 < v₀ / 2 - 2 * M * S r - 2 * (2 * v₀ * S r + 3 * M * S r ^ 2 + 2 * r * S r) -
        2 * (r + 3 * M * S r ^ 2) ∧
      M * (r + 3 * M * S r ^ 2) < (v₀ / 2 - M * S r) * (v₀ / 2 - 3 * M * S r - 2 * r) := by
    have E1 : ∀ᶠ r in 𝓝 (0:ℝ), v₀ / 2 < v r := evt_gt hvc (by rw [hv0]; linarith)
    have E2 : ∀ᶠ r in 𝓝 (0:ℝ), v r < 2 * v₀ := evt_lt hvc (by rw [hv0]; linarith)
    have E3 : ∀ᶠ r in 𝓝 (0:ℝ), 0 < farR μ c r := evt_gt hRc (by rw [farR_zero]; linarith)
    have E4 : ∀ᶠ r in 𝓝 (0:ℝ), 2 * r ^ 2 < 1 := evt_lt (by fun_prop) (by norm_num)
    have E5 : ∀ᶠ r in 𝓝 (0:ℝ), 48 * M * r / v₀ ^ 2 < 1 := evt_lt (by fun_prop) (by simp)
    have E6 : ∀ᶠ r in 𝓝 (0:ℝ), 12 * M * r / v₀ + 2 * r < v₀ / 2 :=
      evt_lt (by fun_prop) (by simp; positivity)
    have E7 : ∀ᶠ r in 𝓝 (0:ℝ), 96 * M * r / v₀ ^ 2 + 8 * r / v₀ < 1 := evt_lt (by fun_prop) (by simp)
    have E8 : ∀ᶠ r in 𝓝 (0:ℝ), 0 < v₀ / 2 - 2 * M * S r -
        2 * (2 * v₀ * S r + 3 * M * S r ^ 2 + 2 * r * S r) - 2 * (r + 3 * M * S r ^ 2) :=
      evt_gt (by fun_prop) (by simp [hSdef]; positivity)
    have E9 : ∀ᶠ r in 𝓝 (0:ℝ),
        M * (r + 3 * M * S r ^ 2) < (v₀ / 2 - M * S r) * (v₀ / 2 - 3 * M * S r - 2 * r) := by
      have := evt_lt (f := fun r => M * (r + 3 * M * S r ^ 2) -
        (v₀ / 2 - M * S r) * (v₀ / 2 - 3 * M * S r - 2 * r)) (b := 0) (by fun_prop)
        (by simp [hSdef]; nlinarith [hv₀0])
      exact this.mono fun r hr => by linarith
    exact E1.and (E2.and (E3.and (E4.and (E5.and (E6.and (E7.and (E8.and E9)))))))
  -- the core estimate applies to every start with these conditions
  have hcore : ∀ r, 0 < r → (v₀ / 2 < v r ∧ v r < 2 * v₀ ∧ 0 < farR μ c r ∧ 2 * r ^ 2 < 1 ∧
      48 * M * r / v₀ ^ 2 < 1 ∧ 12 * M * r / v₀ + 2 * r < v₀ / 2 ∧
      96 * M * r / v₀ ^ 2 + 8 * r / v₀ < 1 ∧
      0 < v₀ / 2 - 2 * M * S r - 2 * (2 * v₀ * S r + 3 * M * S r ^ 2 + 2 * r * S r) -
        2 * (r + 3 * M * S r ^ 2) ∧
      M * (r + 3 * M * S r ^ 2) < (v₀ / 2 - M * S r) * (v₀ / 2 - 3 * M * S r - 2 * r)) →
      ∀ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c r →
      ∃ τ, 0 < τ ∧ τ < S r ∧ IsFarShootingArc φ x τ ∧ (∀ τ', IsFarShootingArc φ x τ' → τ' = τ) ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 0 = -((φ τ x : LeftEnergyState μ c) : Phase) 1 ∧
      0 < ((φ τ x : LeftEnergyState μ c) : Phase) 1 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 1 ≤ r + 3 * M * S r ^ 2 ∧
      |((φ τ x : LeftEnergyState μ c) : Phase) 2 + v r| ≤ M * S r ∧
      |((φ τ x : LeftEnergyState μ c) : Phase) 3| ≤ M * S r := by
    rintro r hr ⟨c1, c2, -, -, c5, c6, c7, c8, c9⟩ x hx
    have hS : S r = 4 * r / v₀ := rfl
    have hSpos : 0 < S r := by rw [hS]; positivity
    apply core_far μ c hμ0 hμ1 hc φ hφ M hM hM0 x r (v r) (S r)
      (by rw [hx]; simp [farShootingStart]) (by rw [hx]; simp [farShootingStart])
      (by rw [hx]; simp [farShootingStart, hvdef, farR]) (by rw [hx]; simp [farShootingStart])
      hr hSpos
    · rw [hS]; field_simp; nlinarith
    · rw [hS]
      have : 3 * M * (4 * r / v₀) ^ 2 = r * (48 * M * r / v₀ ^ 2) := by field_simp; ring
      rw [this]; nlinarith
    · rw [hS]
      have : 3 * M * (4 * r / v₀) = 12 * M * r / v₀ := by ring
      rw [this]; linarith
    · rw [hS]
      have : 6 * M * (4 * r / v₀) ^ 2 + 2 * r * (4 * r / v₀) =
          r * (96 * M * r / v₀ ^ 2 + 8 * r / v₀) := by field_simp; ring
      rw [this]; nlinarith
    · have hvS : v r * S r ≤ 2 * v₀ * S r := mul_le_mul_of_nonneg_right c2.le hSpos.le
      nlinarith
    · have hS' : 3 * M * S r = 12 * M * r / v₀ := by rw [hS]; ring
      have h1 : v₀ / 2 - M * S r ≤ v r - M * S r := by linarith
      have h2 : v₀ / 2 - 3 * M * S r - 2 * r ≤ v r - 3 * M * S r - 2 * r := by linarith
      have h3 : 0 < v₀ / 2 - 3 * M * S r - 2 * r := by rw [hS']; linarith
      have hMS : 0 < M * S r := mul_pos hM0 hSpos
      have := mul_le_mul h1 h2 h3.le (by linarith)
      linarith
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff.1 Ecore
  -- starts in the ball lie on the component
  have hmem : ∀ r, 0 < r → r < δ₀ → farShootingStart μ c r ∈ leftEnergyComponent μ c := by
    intro r hr hrδ
    apply mem_comp_of_path μ c (farShootingStart μ c) 0 r
    · intro r' hr'
      have hr'' : r' ∈ Icc 0 r := by rwa [uIcc_of_le hr.le] at hr'
      exact (farStart_continuous μ c).continuousAt.continuousWithinAt
    · intro r' hr'
      have hr'' : r' ∈ Icc 0 r := by rwa [uIcc_of_le hr.le] at hr'
      obtain ⟨-, -, h3, h4, -⟩ :=
        hball (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hr''.1]; linarith [hr''.2])
      refine ⟨farStart_K μ c r' h3.le, ?_⟩
      rw [farStart_D]; positivity
    · exact farStart_zero_mem μ c hμ0 hμ1
  refine ⟨δ₀, hδ₀, fun r hr => ?_, fun η hη => ?_⟩
  · have hcond := hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hr.1]; exact hr.2)
    obtain ⟨τ, -, -, harc, -⟩ := hcore r hr.1 hcond ⟨_, hmem r hr.1 hr.2⟩ rfl
    exact ⟨_, rfl, τ, harc⟩
  · -- the limiting direction
    obtain ⟨ρ, hρ, hG⟩ := Metric.tendsto_nhds_nhds.1 (Gfar_limit μ hμ1) η hη
    have Elim : ∀ᶠ r in 𝓝 (0:ℝ), r + 3 * M * S r ^ 2 < ρ ∧ M * S r + |v r - v₀| < ρ ∧
        4 * (r + 3 * M * S r ^ 2) ^ 2 < η := by
      refine (evt_lt (by fun_prop) (by simp [hSdef]; exact hρ)).and
        ((evt_lt (f := fun r => M * S r + |v r - v₀|)
          ((by fun_prop : ContinuousAt (fun r => M * S r) 0).add ((hvc.sub continuousAt_const).abs))
          (by simp [hSdef, hv0]; exact hρ)).and
        (evt_lt (by fun_prop) (by simp [hSdef]; exact hη)))
    obtain ⟨δ₁, hδ₁, hball1⟩ := Metric.eventually_nhds_iff.1 Elim
    refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun r hr x τ hx harc => ?_⟩
    have hrd : dist r 0 < min δ₀ δ₁ := by rw [Real.dist_eq, sub_zero, abs_of_pos hr.1]; exact hr.2
    have hcond := hball (lt_of_lt_of_le hrd (min_le_left _ _))
    obtain ⟨l1, l2, l3⟩ := hball1 (lt_of_lt_of_le hrd (min_le_right _ _))
    obtain ⟨τ₀, -, -, -, huniq, hs01, hs0, hs0b, hs2, hs3⟩ := hcore r hr.1 hcond x hx
    have hτ := huniq τ harc
    subst hτ
    set s := ((φ τ x : LeftEnergyState μ c) : Phase)
    have hcoord := coords_far_cross μ s (s 1) hs0 hs01 rfl
    rw [hcoord]
    have hin : dist ((s 1, s 2, s 3) : ℝ × ℝ × ℝ) (0, -v₀, 0) < ρ := by
      rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero,
        sub_neg_eq_add]
      have h3 : |s 2 + v₀| ≤ M * S r + |v r - v₀| := by
        have := abs_add_le (s 2 + v r) (v₀ - v r)
        rw [show s 2 + v r + (v₀ - v r) = s 2 + v₀ by ring, abs_sub_comm] at this; linarith
      dsimp only
      have := abs_nonneg (v r - v₀)
      refine max_lt (by rw [abs_of_pos hs0]; linarith) (max_lt (by linarith) (by linarith))
    have hg := hG hin
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
    refine max_lt (by rwa [Real.dist_eq] at hg) ?_
    rw [abs_of_nonneg (by positivity)]
    have : (s 1) ^ 2 ≤ (r + 3 * M * S r ^ 2) ^ 2 := pow_le_pow_left₀ hs0.le hs0b 2
    linarith
