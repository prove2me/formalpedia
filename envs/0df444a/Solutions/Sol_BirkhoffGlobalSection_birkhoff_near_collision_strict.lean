-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_near_collision_strict
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T14:46:35.488189+00:00
-- url     : https://prove2.me/submissions/757e2eb1-5edc-4da5-b3c8-ce6590681dd1

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

-- ===== Solutions.CM =====
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

lemma line_deriv (f : ℝ → ℝ) (x d : ℝ) (h : HasDerivAt f d x) : deriv f x = d := h.deriv

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

lemma g_alg (μ c a b p q N : ℝ) (hP : a ^ 2 + b ^ 2 ≠ 0) (hN : N ≠ 0)
    (hK : (p ^ 2 + q ^ 2) / 2 + c * (a ^ 2 + b ^ 2) - (1 - μ) / 2 +
      2 * (a ^ 2 + b ^ 2) * (a * q - b * p) - μ * (a * q + b * p) - μ * (a ^ 2 + b ^ 2) / N = 0) :
    let d0 := p - 2 * (a ^ 2 + b ^ 2) * b - μ * b
    let d1 := q + 2 * (a ^ 2 + b ^ 2) * a - μ * a
    let d2 := -(2 * c * a + 4 * a * (a * q - b * p) + 2 * (a ^ 2 + b ^ 2) * q
          - μ * q - μ * (2 * a / N - 4 * (a ^ 2 + b ^ 2) * a * (2 * (a ^ 2 + b ^ 2) - 1) / N ^ 3))
    let d3 := -(2 * c * b + 4 * b * (a * q - b * p) - 2 * (a ^ 2 + b ^ 2) * p
          - μ * p - μ * (2 * b / N - 4 * (a ^ 2 + b ^ 2) * b * (2 * (a ^ 2 + b ^ 2) + 1) / N ^ 3))
    let X := 2 * (a ^ 2 - b ^ 2) - μ
    ((d2 * a + p * d0 - (d3 * b + q * d1)) * (a ^ 2 + b ^ 2) - (p * a - q * b) * (2 * a * d0 + 2 * b * d1))
        / (a ^ 2 + b ^ 2) ^ 2 + (4 * d0 * b + 4 * a * d1) =
      4 * (a ^ 2 + b ^ 2) * (X - (1 - μ) * (X + μ) / (2 * (a ^ 2 + b ^ 2)) ^ 3 -
        μ * (X - 1 + μ) / N ^ 3) := by
  intro d0 d1 d2 d3 X
  simp only [d0, d1, d2, d3, X]
  have hid : ∀ K : ℝ, K = (p ^ 2 + q ^ 2) / 2 + c * (a ^ 2 + b ^ 2) - (1 - μ) / 2 +
      2 * (a ^ 2 + b ^ 2) * (a * q - b * p) - μ * (a * q + b * p) - μ * (a ^ 2 + b ^ 2) / N →
      ((-(2 * c * a + 4 * a * (a * q - b * p) + 2 * (a ^ 2 + b ^ 2) * q
          - μ * q - μ * (2 * a / N - 4 * (a ^ 2 + b ^ 2) * a * (2 * (a ^ 2 + b ^ 2) - 1) / N ^ 3))
          * a + p * (p - 2 * (a ^ 2 + b ^ 2) * b - μ * b)
        - (-(2 * c * b + 4 * b * (a * q - b * p) - 2 * (a ^ 2 + b ^ 2) * p
          - μ * p - μ * (2 * b / N - 4 * (a ^ 2 + b ^ 2) * b * (2 * (a ^ 2 + b ^ 2) + 1) / N ^ 3))
          * b + q * (q + 2 * (a ^ 2 + b ^ 2) * a - μ * a))) * (a ^ 2 + b ^ 2)
        - (p * a - q * b) * (2 * a * (p - 2 * (a ^ 2 + b ^ 2) * b - μ * b)
          + 2 * b * (q + 2 * (a ^ 2 + b ^ 2) * a - μ * a))) / (a ^ 2 + b ^ 2) ^ 2
        + (4 * (p - 2 * (a ^ 2 + b ^ 2) * b - μ * b) * b + 4 * a * (q + 2 * (a ^ 2 + b ^ 2) * a - μ * a))
      - 4 * (a ^ 2 + b ^ 2) * (2 * (a ^ 2 - b ^ 2) - μ - (1 - μ) * (2 * (a ^ 2 - b ^ 2) - μ + μ) /
          (2 * (a ^ 2 + b ^ 2)) ^ 3 - μ * (2 * (a ^ 2 - b ^ 2) - μ - 1 + μ) / N ^ 3)
      + 2 * (a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2) ^ 2 * K = 0 := by
    intro K hK'
    subst hK'
    field_simp
    ring
  have := hid _ rfl
  rw [hK, mul_zero, add_zero, sub_eq_zero] at this
  exact this

/-- Birkhoff's monotone quantity `v₁ + 2 q₂` has derivative `4 |z|² Ω_{q₁}` on the energy level. -/
lemma g_hasDerivAt (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ)
    (hP : 0 < zNormSq ((φ t x : LeftEnergyState μ c) : Phase)) :
    HasDerivAt (fun u : ℝ =>
        (((φ u x : LeftEnergyState μ c) : Phase) 2 * ((φ u x : LeftEnergyState μ c) : Phase) 0 -
          ((φ u x : LeftEnergyState μ c) : Phase) 3 * ((φ u x : LeftEnergyState μ c) : Phase) 1) /
          (((φ u x : LeftEnergyState μ c) : Phase) 0 ^ 2 +
            ((φ u x : LeftEnergyState μ c) : Phase) 1 ^ 2) +
        4 * ((φ u x : LeftEnergyState μ c) : Phase) 0 * ((φ u x : LeftEnergyState μ c) : Phase) 1)
      (4 * zNormSq ((φ t x : LeftEnergyState μ c) : Phase) *
        ((2 * (((φ t x : LeftEnergyState μ c) : Phase) 0 ^ 2 -
            ((φ t x : LeftEnergyState μ c) : Phase) 1 ^ 2) - μ) -
          (1 - μ) * (2 * (((φ t x : LeftEnergyState μ c) : Phase) 0 ^ 2 -
            ((φ t x : LeftEnergyState μ c) : Phase) 1 ^ 2) - μ + μ) /
            Real.sqrt ((2 * (((φ t x : LeftEnergyState μ c) : Phase) 0 ^ 2 -
            ((φ t x : LeftEnergyState μ c) : Phase) 1 ^ 2) - μ + μ) ^ 2 +
              (4 * ((φ t x : LeftEnergyState μ c) : Phase) 0 *
                ((φ t x : LeftEnergyState μ c) : Phase) 1) ^ 2) ^ 3 -
          μ * (2 * (((φ t x : LeftEnergyState μ c) : Phase) 0 ^ 2 -
            ((φ t x : LeftEnergyState μ c) : Phase) 1 ^ 2) - μ - 1 + μ) /
            Real.sqrt ((2 * (((φ t x : LeftEnergyState μ c) : Phase) 0 ^ 2 -
            ((φ t x : LeftEnergyState μ c) : Phase) 1 ^ 2) - μ - 1 + μ) ^ 2 +
              (4 * ((φ t x : LeftEnergyState μ c) : Phase) 0 *
                ((φ t x : LeftEnergyState μ c) : Phase) 1) ^ 2) ^ 3)) t := by
  obtain ⟨h0, h1, h2, h3⟩ := flow_coords μ c φ hφ x t
  have hloc := mem_locus' (φ t x)
  have hK := hloc.1
  have hD := hloc.2
  have hPs0 : ((φ t x : LeftEnergyState μ c) : Phase) 0 ^ 2 +
      ((φ t x : LeftEnergyState μ c) : Phase) 1 ^ 2 ≠ 0 := hP.ne'
  have hnum := ((h2.fun_mul h0).fun_sub (h3.fun_mul h1))
  have hden := ((h0.fun_pow 2).fun_add (h1.fun_pow 2))
  have hall := (hnum.fun_div hden hPs0).fun_add ((h0.const_mul 4).fun_mul h1)
  refine hall.congr_deriv ?_
  clear hall hnum hden h0 h1 h2 h3
  generalize hs : ((φ t x : LeftEnergyState μ c) : Phase) = s at *
  have hPs : s 0 ^ 2 + s 1 ^ 2 ≠ 0 := hPs0
  have r1 : Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) =
      2 * (s 0 ^ 2 + s 1 ^ 2) := by
    rw [show (2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ) ^ 2 + (4 * s 0 * s 1) ^ 2 =
      (2 * (s 0 ^ 2 + s 1 ^ 2)) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have r2 : Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ - 1 + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) =
      Real.sqrt (secondCollisionDistanceSq s) := by
    congr 1; simp only [secondCollisionDistanceSq]; ring
  rw [r1, r2]
  unfold leviCivitaHamiltonian wNormSq zNormSq at hK
  unfold zNormSq
  have hN : Real.sqrt (secondCollisionDistanceSq s) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have := g_alg μ c (s 0) (s 1) (s 2) (s 3) _ hPs hN hK
  simp only at this
  rw [← this]
  ring
/-- The selected component projects into the open disk bounded by the inner Lagrange circle. -/
lemma component_in_L1_disk (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (L : Phase) (hL : IsInnerLagrangePoint μ L)
    (hLval : jacobiHamiltonian μ L = firstCriticalValue μ) :
    ∀ s ∈ leftEnergyComponent μ c,
      (leviCivitaPosition μ s 0 + μ) ^ 2 + (leviCivitaPosition μ s 1) ^ 2 < (L 0 + μ) ^ 2 := by
  intro s hs
  by_contra hge
  push Not at hge
  set f : Phase → ℝ := fun s => (leviCivitaPosition μ s 0 + μ) ^ 2 + (leviCivitaPosition μ s 1) ^ 2
  have hf : Continuous f := by
    simp only [f, leviCivitaPosition]; fun_prop
  have hpre : IsPreconnected (leftEnergyComponent μ c) := isPreconnected_connectedComponentIn
  have h0 := leftCollisionPoint_mem_leftEnergyComponent μ c hμ0 hμ1
  have hf0 : f (leftCollisionPoint μ) = 0 := by
    simp [f, leviCivitaPosition, leftCollisionPoint]
  have hmem : (L 0 + μ) ^ 2 ∈ Icc (f (leftCollisionPoint μ)) (f s) :=
    ⟨by rw [hf0]; positivity, hge⟩
  obtain ⟨s', hs', hfs'⟩ := hpre.intermediate_value h0 hs hf.continuousOn hmem
  have hbound := inner_lagrange_circle_hamiltonian_lower_bound μ hμ0 hμ1 L hL s' hfs'
  have hK : leviCivitaHamiltonian μ c s' = 0 := (connectedComponentIn_subset _ _ hs').1
  have hK0 : leviCivitaHamiltonian μ 0 s' = -c * zNormSq s' := by
    have : leviCivitaHamiltonian μ c s' - leviCivitaHamiltonian μ 0 s' = c * zNormSq s' := by
      unfold leviCivitaHamiltonian; ring
    linarith
  have hLpos : 0 < L 0 + μ := by linarith [hL.2.2.1]
  have hP : 0 < zNormSq s' := by
    have e : f s' = (2 * zNormSq s') ^ 2 := by
      simp only [f, leviCivitaPosition, zNormSq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]; ring
    have hz : 0 ≤ zNormSq s' := by unfold zNormSq; positivity
    rcases hz.lt_or_eq with h | h
    · exact h
    · exfalso; rw [hfs', ← h] at e; simp at e; linarith
  rw [hK0] at hbound
  have : jacobiHamiltonian μ L ≤ -c := by
    have := mul_le_mul_of_nonneg_left (le_refl (1:ℝ)) hP.le
    nlinarith
  unfold belowFirstCriticalValue at hc
  linarith

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

lemma vy_alg (μ c a b p q N : ℝ) (hP : a ^ 2 + b ^ 2 ≠ 0) (hN : N ≠ 0)
    (hK : (p ^ 2 + q ^ 2) / 2 + c * (a ^ 2 + b ^ 2) - (1 - μ) / 2 +
      2 * (a ^ 2 + b ^ 2) * (a * q - b * p) - μ * (a * q + b * p) - μ * (a ^ 2 + b ^ 2) / N = 0) :
    let d0 := p - 2 * (a ^ 2 + b ^ 2) * b - μ * b
    let d1 := q + 2 * (a ^ 2 + b ^ 2) * a - μ * a
    let d2 := -(2 * c * a + 4 * a * (a * q - b * p) + 2 * (a ^ 2 + b ^ 2) * q
          - μ * q - μ * (2 * a / N - 4 * (a ^ 2 + b ^ 2) * a * (2 * (a ^ 2 + b ^ 2) - 1) / N ^ 3))
    let d3 := -(2 * c * b + 4 * b * (a * q - b * p) - 2 * (a ^ 2 + b ^ 2) * p
          - μ * p - μ * (2 * b / N - 4 * (a ^ 2 + b ^ 2) * b * (2 * (a ^ 2 + b ^ 2) + 1) / N ^ 3))
    ((d2 * b + p * d1 + (d3 * a + q * d0)) * (a ^ 2 + b ^ 2) - (p * b + q * a) * (2 * a * d0 + 2 * b * d1))
        / (a ^ 2 + b ^ 2) ^ 2 + 2 * (2 * a * d0 - 2 * b * d1) =
      4 * (a ^ 2 + b ^ 2) * (2 * ((p * a - q * b) / (a ^ 2 + b ^ 2) - 4 * a * b) +
        (4 * a * b - (1 - μ) * (4 * a * b) / (2 * (a ^ 2 + b ^ 2)) ^ 3 -
          μ * (4 * a * b) / N ^ 3)) := by
  intro d0 d1 d2 d3
  simp only [d0, d1, d2, d3]
  have hid : ∀ K : ℝ, K = (p ^ 2 + q ^ 2) / 2 + c * (a ^ 2 + b ^ 2) - (1 - μ) / 2 +
      2 * (a ^ 2 + b ^ 2) * (a * q - b * p) - μ * (a * q + b * p) - μ * (a ^ 2 + b ^ 2) / N →
      ((-(2 * c * a + 4 * a * (a * q - b * p) + 2 * (a ^ 2 + b ^ 2) * q
          - μ * q - μ * (2 * a / N - 4 * (a ^ 2 + b ^ 2) * a * (2 * (a ^ 2 + b ^ 2) - 1) / N ^ 3))
          * b + p * (q + 2 * (a ^ 2 + b ^ 2) * a - μ * a)
        + (-(2 * c * b + 4 * b * (a * q - b * p) - 2 * (a ^ 2 + b ^ 2) * p
          - μ * p - μ * (2 * b / N - 4 * (a ^ 2 + b ^ 2) * b * (2 * (a ^ 2 + b ^ 2) + 1) / N ^ 3))
          * a + q * (p - 2 * (a ^ 2 + b ^ 2) * b - μ * b))) * (a ^ 2 + b ^ 2)
        - (p * b + q * a) * (2 * a * (p - 2 * (a ^ 2 + b ^ 2) * b - μ * b)
          + 2 * b * (q + 2 * (a ^ 2 + b ^ 2) * a - μ * a))) / (a ^ 2 + b ^ 2) ^ 2
        + 2 * (2 * a * (p - 2 * (a ^ 2 + b ^ 2) * b - μ * b) - 2 * b * (q + 2 * (a ^ 2 + b ^ 2) * a - μ * a))
      - 4 * (a ^ 2 + b ^ 2) * (2 * ((p * a - q * b) / (a ^ 2 + b ^ 2) - 4 * a * b) +
        (4 * a * b - (1 - μ) * (4 * a * b) / (2 * (a ^ 2 + b ^ 2)) ^ 3 -
          μ * (4 * a * b) / N ^ 3))
      + 4 * a * b / (a ^ 2 + b ^ 2) ^ 2 * K = 0 := by
    intro K hK'
    subst hK'
    field_simp
    ring
  have := hid _ rfl
  rw [hK, mul_zero, add_zero, sub_eq_zero] at this
  exact this

lemma vy_hasDerivAt (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ)
    (hP : 0 < zNormSq ((φ t x : LeftEnergyState μ c) : Phase)) :
    HasDerivAt (fun u : ℝ => Vy μ ((φ u x : LeftEnergyState μ c) : Phase))
      (4 * zNormSq ((φ t x : LeftEnergyState μ c) : Phase) *
        (2 * Vx ((φ t x : LeftEnergyState μ c) : Phase) +
          Omy μ ((φ t x : LeftEnergyState μ c) : Phase))) t := by
  obtain ⟨h0, h1, h2, h3⟩ := flow_coords μ c φ hφ x t
  have hloc := mem_locus' (φ t x)
  have hK := hloc.1
  have hD := hloc.2
  have hPs0 : ((φ t x : LeftEnergyState μ c) : Phase) 0 ^ 2 +
      ((φ t x : LeftEnergyState μ c) : Phase) 1 ^ 2 ≠ 0 := hP.ne'
  have hnum := ((h2.fun_mul h1).fun_add (h3.fun_mul h0))
  have hden := ((h0.fun_pow 2).fun_add (h1.fun_pow 2))
  have hall := (((hnum.fun_div hden hPs0).fun_add
    (((h0.fun_pow 2).fun_sub (h1.fun_pow 2)).const_mul 2)).sub_const μ)
  unfold Vy
  refine hall.congr_deriv ?_
  clear hall hnum hden h0 h1 h2 h3
  generalize hs : ((φ t x : LeftEnergyState μ c) : Phase) = s at *
  have hPs : s 0 ^ 2 + s 1 ^ 2 ≠ 0 := hPs0
  have r1 : Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) =
      2 * (s 0 ^ 2 + s 1 ^ 2) := by
    rw [show (2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ) ^ 2 + (4 * s 0 * s 1) ^ 2 =
      (2 * (s 0 ^ 2 + s 1 ^ 2)) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have r2 : Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ - 1 + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) =
      Real.sqrt (secondCollisionDistanceSq s) := by
    congr 1; simp only [secondCollisionDistanceSq]; ring
  unfold Omy Vx zNormSq
  rw [r1, r2]
  unfold leviCivitaHamiltonian wNormSq zNormSq at hK
  have hN : Real.sqrt (secondCollisionDistanceSq s) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have := vy_alg μ c (s 0) (s 1) (s 2) (s 3) _ hPs hN hK
  simp only at this
  rw [← this]
  ring

lemma vx_hasDerivAt (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ)
    (hP : 0 < zNormSq ((φ t x : LeftEnergyState μ c) : Phase)) :
    HasDerivAt (fun u : ℝ => Vx ((φ u x : LeftEnergyState μ c) : Phase))
      (4 * zNormSq ((φ t x : LeftEnergyState μ c) : Phase) *
        (Omx μ ((φ t x : LeftEnergyState μ c) : Phase) -
          2 * Vy μ ((φ t x : LeftEnergyState μ c) : Phase))) t := by
  have hg := g_hasDerivAt μ c φ hφ x t hP
  have hy := y_hasDerivAt μ c φ hφ x t
  have hall := hg.fun_sub (hy.const_mul 2)
  have e : (fun u : ℝ => Vx ((φ u x : LeftEnergyState μ c) : Phase)) = fun u =>
      ((((φ u x : LeftEnergyState μ c) : Phase) 2 * ((φ u x : LeftEnergyState μ c) : Phase) 0 -
          ((φ u x : LeftEnergyState μ c) : Phase) 3 * ((φ u x : LeftEnergyState μ c) : Phase) 1) /
          (((φ u x : LeftEnergyState μ c) : Phase) 0 ^ 2 +
            ((φ u x : LeftEnergyState μ c) : Phase) 1 ^ 2) +
        4 * ((φ u x : LeftEnergyState μ c) : Phase) 0 * ((φ u x : LeftEnergyState μ c) : Phase) 1) -
      2 * relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 1 := by
    funext u; simp [Vx, relativePosition, leviCivitaPosition]; ring
  rw [e]
  refine hall.congr_deriv ?_
  have hPs : ((φ t x : LeftEnergyState μ c) : Phase) 0 ^ 2 +
      ((φ t x : LeftEnergyState μ c) : Phase) 1 ^ 2 ≠ 0 := hP.ne'
  rw [Yd_eq μ _ hPs]
  unfold Omx zNormSq
  ring

-- ===== Solutions.CM2 =====
lemma omega_y_pos (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
    (s : Phase) (hs : s ∈ leftEnergyComponent μ c) (hy : 4 * s 0 * s 1 < 0) : 0 < Omy μ s := by
  obtain ⟨L, hL, hLval⟩ := inner_lagrange_realizes_first_critical_value μ hμ0 hμ1
  have hr := component_in_L1_disk μ c hμ0 hμ1 hc L hL hLval s hs
  simp only [leviCivitaPosition, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at hr
  have hpos : 0 < (2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ) ^ 2 + (4 * s 0 * s 1) ^ 2 := by
    have : (4 * s 0 * s 1) ^ 2 > 0 := by nlinarith
    nlinarith [sq_nonneg (2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ)]
  have hT := inner_lagrange_disk_vertical_tidal_factor μ hμ0 hμ1 L hL _ _ hpos hr
  have e : Omy μ s = (4 * s 0 * s 1) * (1 - ((1 - μ) /
      Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) ^ 3 +
      μ / Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ - 1 + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) ^ 3)) := by
    unfold Omy; ring
  rw [e]
  exact mul_pos_of_neg_of_neg hy (by linarith)

/-- The collinear force balance at the inner Lagrange point. -/
lemma lagrange_balance (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase)
    (hL : IsInnerLagrangePoint μ L) :
    0 < L 0 + μ ∧ L 0 + μ < 1 ∧
    (L 0 + μ) - μ - (1 - μ) / (L 0 + μ) ^ 2 + μ / (1 - (L 0 + μ)) ^ 2 = 0 := by
  obtain ⟨hfree, hcrit, hlo, hhi, hL1⟩ := hL
  have hd0 : 0 < L 0 + μ := by linarith
  have hd1 : L 0 + μ < 1 := by linarith
  refine ⟨hd0, hd1, ?_⟩
  have hpart := jacobi_partial_position_one μ L hfree
  have hzero : partialDerivative (jacobiHamiltonian μ) L 0 = 0 := by
    unfold partialDerivative; rw [hcrit.2]; rfl
  have hmom := (jacobi_critical_momentum μ L hcrit).2
  rw [hzero, hmom, hL1] at hpart
  have hs1 : Real.sqrt ((L 0 + μ) ^ 2 + (0:ℝ) ^ 2) = L 0 + μ := by
    rw [zero_pow two_ne_zero, add_zero]; exact Real.sqrt_sq hd0.le
  have hs2 : Real.sqrt ((L 0 - 1 + μ) ^ 2 + (0:ℝ) ^ 2) = 1 - (L 0 + μ) := by
    rw [zero_pow two_ne_zero, add_zero, show (L 0 - 1 + μ) ^ 2 = (1 - (L 0 + μ)) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  rw [hs1, hs2] at hpart
  set d := L 0 + μ with hd
  have hL0 : L 0 = d - μ := by rw [hd]; ring
  rw [hL0] at hpart
  have h1d : 0 < 1 - d := by linarith
  have e1 : (1 - μ) * d / d ^ 3 = (1 - μ) / d ^ 2 := by field_simp
  have e2 : μ * (d - μ - 1 + μ) / (1 - d) ^ 3 = -(μ / (1 - d) ^ 2) := by
    field_simp; ring
  rw [e1, e2] at hpart
  linarith

/-- On the far half-axis inside the inner Lagrange disk the horizontal force is positive. -/
lemma far_axis_omega_x_pos (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (s : Phase) (hs : s ∈ leftEnergyComponent μ c) (h0 : s 0 = 0) (h1 : s 1 ≠ 0) :
    0 < Omx μ s := by
  obtain ⟨L, hL, hLval⟩ := inner_lagrange_realizes_first_critical_value μ hμ0 hμ1
  have hr := component_in_L1_disk μ c hμ0 hμ1 hc L hL hLval s hs
  obtain ⟨hd0, hd1, hbal⟩ := lagrange_balance μ hμ0 hμ1 L hL
  set d := L 0 + μ with hd
  simp only [leviCivitaPosition, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, h0] at hr
  set a := 2 * s 1 ^ 2 with ha
  have ha0 : 0 < a := by positivity
  have had : a < d := by
    have : (2 * (0 ^ 2 - s 1 ^ 2) - μ + μ) ^ 2 + (4 * 0 * s 1) ^ 2 = a ^ 2 := by
      simp only [ha]; ring
    rw [this] at hr
    nlinarith
  have e1 : Real.sqrt ((2 * (0 ^ 2 - s 1 ^ 2) - μ + μ) ^ 2 + (4 * 0 * s 1) ^ 2) = a := by
    rw [show (2 * (0 ^ 2 - s 1 ^ 2) - μ + μ) ^ 2 + (4 * 0 * s 1) ^ 2 = a ^ 2 by
      simp only [ha]; ring]
    exact Real.sqrt_sq ha0.le
  have e2 : Real.sqrt ((2 * (0 ^ 2 - s 1 ^ 2) - μ - 1 + μ) ^ 2 + (4 * 0 * s 1) ^ 2) = 1 + a := by
    rw [show (2 * (0 ^ 2 - s 1 ^ 2) - μ - 1 + μ) ^ 2 + (4 * 0 * s 1) ^ 2 = (1 + a) ^ 2 by
      simp only [ha]; ring]
    exact Real.sqrt_sq (by linarith)
  have e : Omx μ s = -μ - a + (1 - μ) / a ^ 2 + μ / (1 + a) ^ 2 := by
    unfold Omx
    rw [h0, e1, e2]
    have : (2 * (0 ^ 2 - s 1 ^ 2) - μ) = -a - μ := by simp only [ha]; ring
    rw [this]
    field_simp
    ring
  rw [e]
  -- compare with the balance at `L₁`
  have hk1 : (1 - μ) / d ^ 2 < (1 - μ) / a ^ 2 := by
    apply div_lt_div_of_pos_left (by linarith) (by positivity)
    exact pow_lt_pow_left₀ had ha0.le two_ne_zero
  have hk2 : μ / (1 + d) ^ 2 ≤ μ / (1 + a) ^ 2 := by
    apply div_le_div_of_nonneg_left hμ0.le (by positivity)
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hk3 : 2 ≤ 1 / (1 - d) ^ 2 + 1 / (1 + d) ^ 2 := by
    have h1d : 0 < 1 - d := by linarith
    rw [div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
    have h3 : 0 < 3 - d ^ 2 := by nlinarith
    nlinarith [mul_pos (pow_pos hd0 2) h3]
  have hk4 : 2 * μ ≤ μ / (1 - d) ^ 2 + μ / (1 + d) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hk3 hμ0.le
    rw [mul_add, mul_one_div, mul_one_div] at this
    linarith
  linarith

-- ===== Solutions.CM3 =====
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

lemma nearStart_Vy (μ c r : ℝ) (hr : r ≠ 0) :
    Vy μ (nearShootingStart μ c r) = Real.sqrt (nearR μ c r) / r := by
  simp only [Vy, nearStart_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  field_simp; ring

lemma farStart_Vy (μ c r : ℝ) (hr : r ≠ 0) :
    Vy μ (farShootingStart μ c r) = -(Real.sqrt (farR μ c r) / r) := by
  simp only [Vy, farStart_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  field_simp; ring

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

-- ===== Solutions.CM4 =====
/-- A near arc cannot start from rest: the start has positive vertical velocity. -/
lemma near_arc_Vy_pos (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (x : LeftEnergyState μ c) (τ : ℝ)
    (hx1 : (x : Phase) 1 = 0) (hx2 : (x : Phase) 2 = 0) (hx0 : (x : Phase) 0 ≠ 0)
    (harc : IsNearShootingArc φ x τ) : 0 < Vy μ (x : Phase) := by
  obtain ⟨hτ, hq, hend, hcross⟩ := harc
  by_contra hle
  push Not at hle
  set γ : ℝ → Phase := fun t => ((φ t x : LeftEnergyState μ c) : Phase) with hγ
  have hγ0 : γ 0 = (x : Phase) := by simp [hγ]
  have hPpos : ∀ t ∈ Icc (-τ) 0, 0 < zNormSq (γ t) := by
    intro t ht
    unfold zNormSq
    rcases eq_or_lt_of_le ht.2 with h | h
    · subst h; rw [hγ0]; positivity
    have hy : 4 * γ t 0 * γ t 1 < 0 := by
      rcases eq_or_lt_of_le ht.1 with h' | h'
      · subst h'; have := hend; rwa [(relPos_eq μ _).2] at this
      · have := (hq t ⟨h', h⟩).2; rwa [(relPos_eq μ _).2] at this
    have : γ t 0 ≠ 0 := by rintro h0; rw [h0] at hy; simp at hy
    positivity
  -- horizontal velocity positive inside, from the quadrant lemma
  have hVx : ∀ t ∈ Ioo (-τ) 0, 0 < Vx (γ t) := by
    intro t ht
    have hq' : ∀ t' ∈ Ioo (-(-t)) 0,
        0 < relativePosition μ ((φ t' x : LeftEnergyState μ c) : Phase) 0 ∧
        relativePosition μ ((φ t' x : LeftEnergyState μ c) : Phase) 1 < 0 := by
      intro t' ht'
      rw [neg_neg] at ht'
      exact hq t' ⟨by linarith [ht.1, ht'.1], ht'.2⟩
    have hend' : relativePosition μ ((φ (-(-t)) x : LeftEnergyState μ c) : Phase) 1 < 0 := by
      rw [neg_neg]; exact (hq t ht).2
    have := (birkhoff_near_quadrant_monotone μ c hμ0 hμ1 hc φ hφ x (-t) (by linarith [ht.2])
      hx1 hx2 hx0 hq' hend').2
    rw [neg_neg, (jv_eq μ _).1] at this
    exact this
  -- the vertical velocity increases
  have hVyd : ∀ t ∈ Icc (-τ) 0, HasDerivAt (fun u => Vy μ (γ u)) _ t := fun t ht =>
    vy_hasDerivAt μ c φ hφ x t (hPpos t ht)
  have hVymono : StrictMonoOn (fun u => Vy μ (γ u)) (Icc (-τ) 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t ht => (hVyd t ht).continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    rw [(hVyd t (Ioo_subset_Icc_self ht)).deriv]
    have hy : 4 * γ t 0 * γ t 1 < 0 := by
      have := (hq t ht).2; rwa [(relPos_eq μ _).2] at this
    have := omega_y_pos μ c hμ0 hμ1 hc (γ t) (φ t x).2 hy
    have := hVx t ht
    have := hPpos t (Ioo_subset_Icc_self ht)
    positivity
  -- hence the height decreases, contradicting `x₂ < 0` before the start
  have hyd : ∀ t, HasDerivAt (fun u => relativePosition μ (γ u) 1) (Yd μ (γ t)) t :=
    fun t => y_hasDerivAt μ c φ hφ x t
  have hyanti : StrictAntiOn (fun u => relativePosition μ (γ u) 1) (Icc (-τ) 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t _ => (hyd t).continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    rw [(hyd t).deriv]
    have hP := hPpos t (Ioo_subset_Icc_self ht)
    rw [Yd_eq μ _ hP.ne']
    have hv : Vy μ (γ t) < 0 := by
      have := hVymono (Ioo_subset_Icc_self ht) ⟨by linarith [ht.1, ht.2], le_refl _⟩ ht.2
      simp only at this; rw [hγ0] at this; linarith
    unfold zNormSq at hP
    nlinarith
  have := hyanti ⟨by linarith, by linarith⟩ ⟨by linarith, le_refl _⟩ (by linarith : -τ / 2 < 0)
  simp only at this
  have h0 : relativePosition μ (γ 0) 1 = 0 := by rw [hγ0, (relPos_eq μ _).2, hx1]; ring
  rw [h0] at this
  have := (hq (-τ / 2) ⟨by linarith, by linarith⟩).2
  simp only [hγ] at *
  linarith

/-- A far arc cannot start from rest: the start has negative vertical velocity. -/
lemma far_arc_Vy_neg (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (x : LeftEnergyState μ c) (τ : ℝ)
    (hx0 : (x : Phase) 0 = 0) (hx1 : (x : Phase) 1 ≠ 0)
    (harc : IsFarShootingArc φ x τ) : Vy μ (x : Phase) < 0 := by
  obtain ⟨hτ, hlow, hend, hcross, hv⟩ := harc
  by_contra hge
  push Not at hge
  set γ : ℝ → Phase := fun t => ((φ t x : LeftEnergyState μ c) : Phase) with hγ
  have hγ0 : γ 0 = (x : Phase) := by simp [hγ]
  have hylt : ∀ t ∈ Ioc 0 τ, 4 * γ t 0 * γ t 1 < 0 := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · subst h; have := hend; rwa [(relPos_eq μ _).2] at this
    · have := hlow t ⟨ht.1, h⟩; rwa [(relPos_eq μ _).2] at this
  have hPpos : ∀ t ∈ Icc 0 τ, 0 < zNormSq (γ t) := by
    intro t ht
    unfold zNormSq
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h; rw [hγ0]; positivity
    have hy := hylt t ⟨h, ht.2⟩
    have : γ t 0 ≠ 0 := by rintro h0; rw [h0] at hy; simp at hy
    positivity
  have hVyd : ∀ t ∈ Icc 0 τ, HasDerivAt (fun u => Vy μ (γ u)) _ t := fun t ht =>
    vy_hasDerivAt μ c φ hφ x t (hPpos t ht)
  have hVymono : StrictMonoOn (fun u => Vy μ (γ u)) (Icc 0 τ) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t ht => (hVyd t ht).continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    rw [(hVyd t (Ioo_subset_Icc_self ht)).deriv]
    have := omega_y_pos μ c hμ0 hμ1 hc (γ t) (φ t x).2 (hylt t ⟨ht.1, ht.2.le⟩)
    have hvx := hv t ⟨ht.1, ht.2.le⟩
    rw [(jv_eq μ _).1] at hvx
    have := hPpos t (Ioo_subset_Icc_self ht)
    simp only [hγ] at *
    positivity
  have hyd : ∀ t, HasDerivAt (fun u => relativePosition μ (γ u) 1) (Yd μ (γ t)) t :=
    fun t => y_hasDerivAt μ c φ hφ x t
  have hymono : StrictMonoOn (fun u => relativePosition μ (γ u) 1) (Icc 0 τ) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t _ => (hyd t).continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    rw [(hyd t).deriv]
    have hP := hPpos t (Ioo_subset_Icc_self ht)
    rw [Yd_eq μ _ hP.ne']
    have hvy : 0 < Vy μ (γ t) := by
      have := hVymono ⟨le_refl _, hτ.le⟩ (Ioo_subset_Icc_self ht) ht.1
      simp only at this; rw [hγ0] at this; linarith
    unfold zNormSq at hP
    positivity
  have := hymono ⟨le_refl _, hτ.le⟩ ⟨by linarith, by linarith⟩ (by linarith : (0:ℝ) < τ / 2)
  simp only at this
  have h0 : relativePosition μ (γ 0) 1 = 0 := by rw [hγ0, (relPos_eq μ _).2, hx0]; ring
  rw [h0] at this
  have := hlow (τ / 2) ⟨by linarith, by linarith⟩
  simp only [hγ] at *
  linarith

-- ===== Solutions.CM5 =====
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

lemma cont_Omx (μ : ℝ) (s : Phase) (hP : s 0 ^ 2 + s 1 ^ 2 ≠ 0)
    (hD : 0 < secondCollisionDistanceSq s) : ContinuousAt (Omx μ) s := by
  have h1 : Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) ^ 3 ≠ 0 := by
    apply pow_ne_zero; apply (Real.sqrt_pos.2 _).ne'
    have : (2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ) ^ 2 + (4 * s 0 * s 1) ^ 2 =
      (2 * (s 0 ^ 2 + s 1 ^ 2)) ^ 2 := by ring
    rw [this]; positivity
  have h2 : Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ - 1 + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) ^ 3 ≠ 0 := by
    apply pow_ne_zero; apply (Real.sqrt_pos.2 _).ne'
    have : (2 * (s 0 ^ 2 - s 1 ^ 2) - μ - 1 + μ) ^ 2 + (4 * s 0 * s 1) ^ 2 =
      secondCollisionDistanceSq s := by unfold secondCollisionDistanceSq; ring
    rw [this]; exact hD
  unfold Omx
  apply ContinuousAt.sub
  apply ContinuousAt.sub
  · fun_prop
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) h1
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) h2

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

/-- The time-`(±s)` state along the flow from a family of starts. -/
lemma flow_state_continuousAt {μ c : ℝ} (φ : Flow ℝ (LeftEnergyState μ c))
    (Sx : ℝ → LeftEnergyState μ c) (r₀ : ℝ) (hS : ContinuousAt Sx r₀) (σ : ℝ) (s : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => ((φ (σ * q.1) (Sx q.2) : LeftEnergyState μ c) : Phase))
      (s, r₀) := by
  have hpair : ContinuousAt (fun q : ℝ × ℝ => (σ * q.1, Sx q.2)) (s, r₀) :=
    ContinuousAt.prodMk (by fun_prop) (hS.comp continuousAt_snd)
  exact continuous_subtype_val.continuousAt.comp (φ.cont'.continuousAt.comp hpair)

/-- Starts depending on a real parameter, continuous where they lie on the component. -/
lemma start_family {μ c : ℝ} (St : ℝ → Phase) (x₀ : LeftEnergyState μ c) (r₀ : ℝ)
    (hx₀ : (x₀ : Phase) = St r₀) (hSt : ContinuousAt St r₀)
    (hmem : ∀ᶠ r in 𝓝 r₀, St r ∈ leftEnergyComponent μ c) :
    ∃ Sx : ℝ → LeftEnergyState μ c, Sx r₀ = x₀ ∧ ContinuousAt Sx r₀ ∧
      (∀ᶠ r in 𝓝 r₀, (Sx r : Phase) = St r) ∧ (∀ r, (Sx r : Phase) = St r ∨ Sx r = x₀) := by
  classical
  refine ⟨fun r => if h : St r ∈ leftEnergyComponent μ c then ⟨St r, h⟩ else x₀, ?_, ?_, ?_, ?_⟩
  · have h : St r₀ ∈ leftEnergyComponent μ c := hx₀ ▸ x₀.2
    simp only [h, dif_pos]; exact Subtype.ext hx₀.symm
  · rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
    apply hSt.congr
    filter_upwards [hmem] with r hr
    simp [hr]
  · filter_upwards [hmem] with r hr
    simp [hr]
  · intro r
    by_cases h : St r ∈ leftEnergyComponent μ c
    · left; simp [h]
    · right; simp [h]

-- ===== Solutions.CM8 =====
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

-- ===== Solutions.CM13 =====
noncomputable def g1f (μ c : ℝ) (s : Phase) : ℝ :=
  -2 * c - 4 * (s 0 * s 3 - s 1 * s 2) +
    μ * (2 / Real.sqrt (secondCollisionDistanceSq s) -
      4 * (s 0 ^ 2 + s 1 ^ 2) * (2 * (s 0 ^ 2 + s 1 ^ 2) + 1) /
        Real.sqrt (secondCollisionDistanceSq s) ^ 3) +
    2 * μ * (s 0 ^ 2 + s 1 ^ 2) + μ ^ 2

noncomputable def h1f (μ c : ℝ) (s : Phase) : ℝ :=
  -2 * c - 4 * (s 0 * s 3 - s 1 * s 2) +
    μ * (2 / Real.sqrt (secondCollisionDistanceSq s) -
      4 * (s 0 ^ 2 + s 1 ^ 2) * (2 * (s 0 ^ 2 + s 1 ^ 2) - 1) /
        Real.sqrt (secondCollisionDistanceSq s) ^ 3) -
    2 * μ * (s 0 ^ 2 + s 1 ^ 2) + μ ^ 2

lemma Xq_sub (μ c : ℝ) (s : Phase) :
    Xq μ c s - μ * Xa μ s = s 1 * g1f μ c s + (s 0 ^ 2 + s 1 ^ 2) * (2 * s 2) := by
  unfold Xq Xa g1f; ring

lemma Xp_sub (μ c : ℝ) (s : Phase) :
    Xp μ c s - μ * Xb μ s = s 0 * h1f μ c s - (s 0 ^ 2 + s 1 ^ 2) * (2 * s 3) := by
  unfold Xp Xb h1f; ring

lemma cont_g1 (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s) :
    ContinuousAt (g1f μ c) s := by
  have hN : Real.sqrt (secondCollisionDistanceSq s) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have hN3 : Real.sqrt (secondCollisionDistanceSq s) ^ 3 ≠ 0 := pow_ne_zero _ hN
  unfold g1f secondCollisionDistanceSq at *
  fun_prop (disch := first | exact hN | exact hN3)

lemma cont_h1 (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s) :
    ContinuousAt (h1f μ c) s := by
  have hN : Real.sqrt (secondCollisionDistanceSq s) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have hN3 : Real.sqrt (secondCollisionDistanceSq s) ^ 3 ≠ 0 := pow_ne_zero _ hN
  unfold h1f secondCollisionDistanceSq at *
  fun_prop (disch := first | exact hN | exact hN3)

/-- Uniform bounds for the collision estimates on the compact component. -/
lemma coll_bounds (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c) :
    ∃ C > 0, ∀ s ∈ leftEnergyComponent μ c,
      |g1f μ c s| ≤ C ∧ |h1f μ c s| ≤ C ∧ |s 2| ≤ C ∧ |s 3| ≤ C := by
  have hK := left_energy_component_compact μ c hμ0 hμ1 hc
  have hD : ∀ s ∈ leftEnergyComponent μ c, 0 < secondCollisionDistanceSq s := fun s hs =>
    (connectedComponentIn_subset _ _ hs).2
  obtain ⟨C1, h1⟩ := hK.exists_bound_of_continuousOn
    (fun s hs => (cont_g1 μ c s (hD s hs)).continuousWithinAt)
  obtain ⟨C2, h2⟩ := hK.exists_bound_of_continuousOn
    (fun s hs => (cont_h1 μ c s (hD s hs)).continuousWithinAt)
  obtain ⟨C3, h3⟩ := hK.exists_bound_of_continuousOn
    (continuous_apply (2 : Fin 4)).continuousOn
  obtain ⟨C4, h4⟩ := hK.exists_bound_of_continuousOn
    (continuous_apply (3 : Fin 4)).continuousOn
  have h0 := leftCollisionPoint_mem_leftEnergyComponent μ c hμ0 hμ1
  refine ⟨max (max C1 C2) (max C3 C4) + 1, by
    have := le_trans (norm_nonneg _) (h1 _ h0)
    positivity, fun s hs => ⟨?_, ?_, ?_, ?_⟩⟩
  · have := h1 s hs; rw [Real.norm_eq_abs] at this
    linarith [le_max_left C1 C2, le_max_left (max C1 C2) (max C3 C4)]
  · have := h2 s hs; rw [Real.norm_eq_abs] at this
    linarith [le_max_right C1 C2, le_max_left (max C1 C2) (max C3 C4)]
  · have := h3 s hs; rw [Real.norm_eq_abs] at this
    linarith [le_max_left C3 C4, le_max_right (max C1 C2) (max C3 C4)]
  · have := h4 s hs; rw [Real.norm_eq_abs] at this
    linarith [le_max_right C3 C4, le_max_right (max C1 C2) (max C3 C4)]

/-- Estimates near a collision state `z = 0`, `w = (w₀, 0)`. -/
lemma coll_est_near (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (M : ℝ) (hM : ∀ s ∈ leftEnergyComponent μ c,
      |Xa μ s| ≤ M ∧ |Xb μ s| ≤ M ∧ |Xp μ c s| ≤ M ∧ |Xq μ c s| ≤ M) (hM0 : 0 < M)
    (C : ℝ) (hC : ∀ s ∈ leftEnergyComponent μ c,
      |g1f μ c s| ≤ C ∧ |h1f μ c s| ≤ C ∧ |s 2| ≤ C ∧ |s 3| ≤ C)
    (x : LeftEnergyState μ c) (h0 : (x : Phase) 0 = 0) (h1 : (x : Phase) 1 = 0)
    (h3 : (x : Phase) 3 = 0) (s t : ℝ) (ht : |t| ≤ s) (hs1 : s ≤ 1) :
    |((φ t x : LeftEnergyState μ c) : Phase) 3 - μ * ((φ t x : LeftEnergyState μ c) : Phase) 0| ≤
      C * (M + 4 * M ^ 2) * s ^ 2 ∧
    |((φ t x : LeftEnergyState μ c) : Phase) 1| ≤ (C * (M + 4 * M ^ 2) + 4 * M ^ 3) * s ^ 3 := by
  set γ : ℝ → Phase := fun u => ((φ u x : LeftEnergyState μ c) : Phase) with hγ
  have hγ0 : γ 0 = (x : Phase) := by simp [hγ]
  have hs : 0 ≤ s := le_trans (abs_nonneg _) ht
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC _ x.2).1
  have hd := fun u => flow_coords' μ c φ hφ x u
  have first : ∀ u, |u| ≤ s → |γ u 0| ≤ M * s ∧ |γ u 1| ≤ M * s := by
    intro u hu
    obtain ⟨e0, e1, -⟩ := flow_estimates μ c hμ0 hμ1 hc φ hφ M hM x s u hu
    rw [h0] at e0; rw [h1] at e1
    simp only [sub_zero] at e0 e1
    exact ⟨e0, e1⟩
  have hP : ∀ u, |u| ≤ s → γ u 0 ^ 2 + γ u 1 ^ 2 ≤ 2 * M ^ 2 * s ^ 2 := by
    intro u hu
    obtain ⟨a0, a1⟩ := first u hu
    have := sq_le_sq' (abs_le.1 a0).1 (abs_le.1 a0).2
    have := sq_le_sq' (abs_le.1 a1).1 (abs_le.1 a1).2
    nlinarith
  have part1 : ∀ u, |u| ≤ s → |γ u 3 - μ * γ u 0| ≤ C * (M + 4 * M ^ 2) * s ^ 2 := by
    intro u hu
    have := mvt_bound (fun v => γ v 3 - μ * γ v 0) (fun v => Xq μ c (γ v) - μ * Xa μ (γ v))
      (C * (M + 4 * M ^ 2) * s) s u hu
      (fun v _ => (hd v).2.2.2.sub ((hd v).1.const_mul μ))
      (fun v hv => by
        have hv' : |v| ≤ s := abs_le.2 hv
        rw [Xq_sub]
        obtain ⟨-, a1⟩ := first v hv'
        obtain ⟨cg, -, cp, -⟩ := hC _ (φ v x).2
        have hPv := hP v hv'
        have hPnn : 0 ≤ γ v 0 ^ 2 + γ v 1 ^ 2 := by positivity
        calc |γ v 1 * g1f μ c (γ v) + (γ v 0 ^ 2 + γ v 1 ^ 2) * (2 * γ v 2)|
            ≤ |γ v 1| * |g1f μ c (γ v)| + (γ v 0 ^ 2 + γ v 1 ^ 2) * (2 * |γ v 2|) := by
              refine le_trans (abs_add_le _ _) ?_
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hPnn, abs_two]
          _ ≤ (M * s) * C + (2 * M ^ 2 * s ^ 2) * (2 * C) := by
              gcongr
          _ ≤ C * (M + 4 * M ^ 2) * s := by
              have : s ^ 2 ≤ s := by nlinarith
              nlinarith [mul_nonneg hC0 (sq_nonneg M)])
    simp only [hγ0, h0, h3, mul_zero, sub_zero] at this
    have e : C * (M + 4 * M ^ 2) * s * s = C * (M + 4 * M ^ 2) * s ^ 2 := by ring
    simpa [hγ, e] using this
  refine ⟨part1 t ht, ?_⟩
  have := mvt_bound (fun v => γ v 1) (fun v => Xb μ (γ v))
    ((C * (M + 4 * M ^ 2) + 4 * M ^ 3) * s ^ 2) s t ht
    (fun v _ => (hd v).2.1)
    (fun v hv => by
      have hv' : |v| ≤ s := abs_le.2 hv
      have e : Xb μ (γ v) = (γ v 3 - μ * γ v 0) + 2 * (γ v 0 ^ 2 + γ v 1 ^ 2) * γ v 0 := by
        unfold Xb; ring
      rw [e]
      have p1 := part1 v hv'
      obtain ⟨a0, -⟩ := first v hv'
      have hPv := hP v hv'
      have hPnn : 0 ≤ γ v 0 ^ 2 + γ v 1 ^ 2 := by positivity
      calc |(γ v 3 - μ * γ v 0) + 2 * (γ v 0 ^ 2 + γ v 1 ^ 2) * γ v 0|
          ≤ |γ v 3 - μ * γ v 0| + 2 * (γ v 0 ^ 2 + γ v 1 ^ 2) * |γ v 0| := by
            refine le_trans (abs_add_le _ _) ?_
            rw [abs_mul, abs_mul, abs_of_nonneg hPnn, abs_two]
        _ ≤ C * (M + 4 * M ^ 2) * s ^ 2 + 2 * (2 * M ^ 2 * s ^ 2) * (M * s) := by gcongr
        _ ≤ (C * (M + 4 * M ^ 2) + 4 * M ^ 3) * s ^ 2 := by
            have : s ^ 3 ≤ s ^ 2 := by nlinarith [sq_nonneg s]
            nlinarith [pow_pos hM0 3])
  simp only [hγ0, h1, sub_zero] at this
  have e : (C * (M + 4 * M ^ 2) + 4 * M ^ 3) * s ^ 2 * s = (C * (M + 4 * M ^ 2) + 4 * M ^ 3) * s ^ 3 := by
    ring
  simpa [hγ, e] using this

/-- Estimates near a collision state `z = 0`, `w = (0, w₁)`. -/
lemma coll_est_far (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (M : ℝ) (hM : ∀ s ∈ leftEnergyComponent μ c,
      |Xa μ s| ≤ M ∧ |Xb μ s| ≤ M ∧ |Xp μ c s| ≤ M ∧ |Xq μ c s| ≤ M) (hM0 : 0 < M)
    (C : ℝ) (hC : ∀ s ∈ leftEnergyComponent μ c,
      |g1f μ c s| ≤ C ∧ |h1f μ c s| ≤ C ∧ |s 2| ≤ C ∧ |s 3| ≤ C)
    (x : LeftEnergyState μ c) (h0 : (x : Phase) 0 = 0) (h1 : (x : Phase) 1 = 0)
    (h2 : (x : Phase) 2 = 0) (s t : ℝ) (ht : |t| ≤ s) (hs1 : s ≤ 1) :
    |((φ t x : LeftEnergyState μ c) : Phase) 2 - μ * ((φ t x : LeftEnergyState μ c) : Phase) 1| ≤
      C * (M + 4 * M ^ 2) * s ^ 2 ∧
    |((φ t x : LeftEnergyState μ c) : Phase) 0| ≤ (C * (M + 4 * M ^ 2) + 4 * M ^ 3) * s ^ 3 := by
  set γ : ℝ → Phase := fun u => ((φ u x : LeftEnergyState μ c) : Phase) with hγ
  have hγ0 : γ 0 = (x : Phase) := by simp [hγ]
  have hs : 0 ≤ s := le_trans (abs_nonneg _) ht
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC _ x.2).1
  have hd := fun u => flow_coords' μ c φ hφ x u
  have first : ∀ u, |u| ≤ s → |γ u 0| ≤ M * s ∧ |γ u 1| ≤ M * s := by
    intro u hu
    obtain ⟨e0, e1, -⟩ := flow_estimates μ c hμ0 hμ1 hc φ hφ M hM x s u hu
    rw [h0] at e0; rw [h1] at e1
    simp only [sub_zero] at e0 e1
    exact ⟨e0, e1⟩
  have hP : ∀ u, |u| ≤ s → γ u 0 ^ 2 + γ u 1 ^ 2 ≤ 2 * M ^ 2 * s ^ 2 := by
    intro u hu
    obtain ⟨a0, a1⟩ := first u hu
    have := sq_le_sq' (abs_le.1 a0).1 (abs_le.1 a0).2
    have := sq_le_sq' (abs_le.1 a1).1 (abs_le.1 a1).2
    nlinarith
  have part1 : ∀ u, |u| ≤ s → |γ u 2 - μ * γ u 1| ≤ C * (M + 4 * M ^ 2) * s ^ 2 := by
    intro u hu
    have := mvt_bound (fun v => γ v 2 - μ * γ v 1) (fun v => Xp μ c (γ v) - μ * Xb μ (γ v))
      (C * (M + 4 * M ^ 2) * s) s u hu
      (fun v _ => (hd v).2.2.1.sub ((hd v).2.1.const_mul μ))
      (fun v hv => by
        have hv' : |v| ≤ s := abs_le.2 hv
        rw [Xp_sub]
        obtain ⟨a1, -⟩ := first v hv'
        obtain ⟨-, cg, -, cp⟩ := hC _ (φ v x).2
        have hPv := hP v hv'
        have hPnn : 0 ≤ γ v 0 ^ 2 + γ v 1 ^ 2 := by positivity
        calc |γ v 0 * h1f μ c (γ v) - (γ v 0 ^ 2 + γ v 1 ^ 2) * (2 * γ v 3)|
            ≤ |γ v 0| * |h1f μ c (γ v)| + (γ v 0 ^ 2 + γ v 1 ^ 2) * (2 * |γ v 3|) := by
              refine le_trans (abs_sub _ _) ?_
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hPnn, abs_two]
          _ ≤ (M * s) * C + (2 * M ^ 2 * s ^ 2) * (2 * C) := by
              gcongr
          _ ≤ C * (M + 4 * M ^ 2) * s := by
              have : s ^ 2 ≤ s := by nlinarith
              nlinarith [mul_nonneg hC0 (sq_nonneg M)])
    simp only [hγ0, h1, h2, mul_zero, sub_zero] at this
    have e : C * (M + 4 * M ^ 2) * s * s = C * (M + 4 * M ^ 2) * s ^ 2 := by ring
    simpa [hγ, e] using this
  refine ⟨part1 t ht, ?_⟩
  have := mvt_bound (fun v => γ v 0) (fun v => Xa μ (γ v))
    ((C * (M + 4 * M ^ 2) + 4 * M ^ 3) * s ^ 2) s t ht
    (fun v _ => (hd v).1)
    (fun v hv => by
      have hv' : |v| ≤ s := abs_le.2 hv
      have e : Xa μ (γ v) = (γ v 2 - μ * γ v 1) - 2 * (γ v 0 ^ 2 + γ v 1 ^ 2) * γ v 1 := by
        unfold Xa; ring
      rw [e]
      have p1 := part1 v hv'
      obtain ⟨-, a0⟩ := first v hv'
      have hPv := hP v hv'
      have hPnn : 0 ≤ γ v 0 ^ 2 + γ v 1 ^ 2 := by positivity
      calc |(γ v 2 - μ * γ v 1) - 2 * (γ v 0 ^ 2 + γ v 1 ^ 2) * γ v 1|
          ≤ |γ v 2 - μ * γ v 1| + 2 * (γ v 0 ^ 2 + γ v 1 ^ 2) * |γ v 1| := by
            refine le_trans (abs_sub _ _) ?_
            rw [abs_mul, abs_mul, abs_of_nonneg hPnn, abs_two]
        _ ≤ C * (M + 4 * M ^ 2) * s ^ 2 + 2 * (2 * M ^ 2 * s ^ 2) * (M * s) := by gcongr
        _ ≤ (C * (M + 4 * M ^ 2) + 4 * M ^ 3) * s ^ 2 := by
            have : s ^ 3 ≤ s ^ 2 := by nlinarith [sq_nonneg s]
            nlinarith [pow_pos hM0 3])
  simp only [hγ0, h0, sub_zero] at this
  have e : (C * (M + 4 * M ^ 2) + 4 * M ^ 3) * s ^ 2 * s = (C * (M + 4 * M ^ 2) + 4 * M ^ 3) * s ^ 3 := by
    ring
  simpa [hγ, e] using this

-- ===== Solutions.CM14 =====
/-- Energy at a collision state fixes the speed. -/
lemma collision_speed (μ c : ℝ) (s : Phase) (hs : s ∈ leftEnergyComponent μ c)
    (h0 : s 0 = 0) (h1 : s 1 = 0) : s 2 ^ 2 + s 3 ^ 2 = 1 - μ := by
  have hK := (connectedComponentIn_subset _ _ hs).1
  simp only [leviCivitaHamiltonian, wNormSq, zNormSq, h0, h1] at hK
  simp at hK
  linarith

set_option maxHeartbeats 1000000 in
/-- Near-collision estimate of `v₂` when the collision velocity is horizontal. -/
lemma Vy_small_near (μ M C w0 s a b p q : ℝ) (hM0 : 0 < M) (hw0 : 0 < w0)
    (hs0 : 0 < s) (hs1 : s ≤ 1)
    (ha1 : w0 / 2 * s ≤ a) (ha2 : a ≤ M * s)
    (hb : |b| ≤ (C * (M + 4 * M ^ 2) + 4 * M ^ 3) * s ^ 3)
    (hq : |q - μ * a| ≤ C * (M + 4 * M ^ 2) * s ^ 2) (hp : |p| ≤ C) (hC : 0 ≤ C)
    (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    |(p * b + q * a) / (a ^ 2 + b ^ 2) + 2 * (a ^ 2 - b ^ 2) - μ| ≤ (4 * (C * (C * (M + 4 * M ^ 2) + 4 * M ^ 3) + C * (M + 4 * M ^ 2) * M +
      (C * (M + 4 * M ^ 2) + 4 * M ^ 3) ^ 2) / w0 ^ 2 +
      2 * (M ^ 2 + (C * (M + 4 * M ^ 2) + 4 * M ^ 3) ^ 2)) * s := by
  set K1 := C * (M + 4 * M ^ 2) with hK1
  set K2 := C * (M + 4 * M ^ 2) + 4 * M ^ 3 with hK2
  have hK1n : 0 ≤ K1 := by positivity
  have hK2n : 0 ≤ K2 := by positivity
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha1
  have hP : 0 < a ^ 2 + b ^ 2 := by positivity
  have hPlow : (w0 / 2 * s) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) ha1 2; nlinarith [sq_nonneg b]
  have e : (p * b + q * a) / (a ^ 2 + b ^ 2) + 2 * (a ^ 2 - b ^ 2) - μ =
      (p * b + (q - μ * a) * a - μ * b ^ 2) / (a ^ 2 + b ^ 2) + 2 * (a ^ 2 - b ^ 2) := by
    have hP' : a ^ 2 + b ^ 2 ≠ 0 := hP.ne'
    field_simp
    ring
  rw [e]
  have hs3 : s ^ 3 ≤ s ^ 2 := by nlinarith [sq_nonneg s]
  have hs6 : s ^ 6 ≤ s ^ 3 := by
    have : s ^ 3 ≤ 1 := pow_le_one₀ hs0.le hs1
    nlinarith [pow_pos hs0 3]
  have hbb : b ^ 2 ≤ K2 ^ 2 * s ^ 6 := by
    have := sq_le_sq' (abs_le.1 hb).1 (abs_le.1 hb).2
    calc b ^ 2 ≤ (K2 * s ^ 3) ^ 2 := this
      _ = K2 ^ 2 * s ^ 6 := by ring
  have hnum : |p * b + (q - μ * a) * a - μ * b ^ 2| ≤ (C * K2 + K1 * M + K2 ^ 2) * s ^ 3 := by
    have t1 : |p * b| ≤ C * (K2 * s ^ 3) := by
      rw [abs_mul]; exact mul_le_mul hp hb (abs_nonneg _) hC
    have t2 : |(q - μ * a) * a| ≤ (K1 * s ^ 2) * (M * s) := by
      rw [abs_mul, abs_of_pos ha0]; exact mul_le_mul hq ha2 ha0.le (by positivity)
    have t3 : |μ * b ^ 2| ≤ K2 ^ 2 * s ^ 3 := by
      rw [abs_of_nonneg (by positivity)]
      calc μ * b ^ 2 ≤ 1 * (K2 ^ 2 * s ^ 6) := mul_le_mul hμ1 hbb (sq_nonneg _) zero_le_one
        _ ≤ K2 ^ 2 * s ^ 3 := by nlinarith [sq_nonneg K2]
    calc |p * b + (q - μ * a) * a - μ * b ^ 2| ≤ |p * b| + |(q - μ * a) * a| + |μ * b ^ 2| := by
          refine le_trans (abs_sub _ _) ?_
          gcongr; exact abs_add_le _ _
      _ ≤ C * (K2 * s ^ 3) + (K1 * s ^ 2) * (M * s) + K2 ^ 2 * s ^ 3 := by gcongr
      _ = (C * K2 + K1 * M + K2 ^ 2) * s ^ 3 := by ring
  have hfrac : |(p * b + (q - μ * a) * a - μ * b ^ 2) / (a ^ 2 + b ^ 2)| ≤
      4 * (C * K2 + K1 * M + K2 ^ 2) / w0 ^ 2 * s := by
    rw [abs_div, abs_of_pos hP, div_le_iff₀ hP]
    calc |p * b + (q - μ * a) * a - μ * b ^ 2| ≤ (C * K2 + K1 * M + K2 ^ 2) * s ^ 3 := hnum
      _ = 4 * (C * K2 + K1 * M + K2 ^ 2) / w0 ^ 2 * s * (w0 / 2 * s) ^ 2 := by
          field_simp; ring
      _ ≤ 4 * (C * K2 + K1 * M + K2 ^ 2) / w0 ^ 2 * s * (a ^ 2 + b ^ 2) := by
          gcongr
  have hsq : |2 * (a ^ 2 - b ^ 2)| ≤ 2 * (M ^ 2 + K2 ^ 2) * s := by
    have h1 : a ^ 2 ≤ M ^ 2 * s ^ 2 := by
      have := pow_le_pow_left₀ ha0.le ha2 2; nlinarith
    have h2 : s ^ 2 ≤ s := by nlinarith
    have h3 : a ^ 2 + b ^ 2 ≤ (M ^ 2 + K2 ^ 2) * s := by
      have x1 : M ^ 2 * s ^ 2 ≤ M ^ 2 * s := mul_le_mul_of_nonneg_left h2 (sq_nonneg M)
      have x2 : K2 ^ 2 * s ^ 6 ≤ K2 ^ 2 * s := by
        have : s ^ 6 ≤ s := le_trans hs6 (le_trans hs3 h2)
        exact mul_le_mul_of_nonneg_left this (sq_nonneg K2)
      have e2 : (M ^ 2 + K2 ^ 2) * s = M ^ 2 * s + K2 ^ 2 * s := by ring
      linarith
    have hb0 := sq_nonneg b
    have ha0' := sq_nonneg a
    rw [abs_le]; constructor <;> linarith
  calc |(p * b + (q - μ * a) * a - μ * b ^ 2) / (a ^ 2 + b ^ 2) + 2 * (a ^ 2 - b ^ 2)|
      ≤ |(p * b + (q - μ * a) * a - μ * b ^ 2) / (a ^ 2 + b ^ 2)| + |2 * (a ^ 2 - b ^ 2)| :=
        abs_add_le _ _
    _ ≤ 4 * (C * K2 + K1 * M + K2 ^ 2) / w0 ^ 2 * s + 2 * (M ^ 2 + K2 ^ 2) * s := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
lemma Vy_small_far (μ M C w0 s a b p q : ℝ) (hM0 : 0 < M) (hw0 : 0 < w0)
    (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hb1 : w0 / 2 * s ≤ |b|) (hb2 : |b| ≤ M * s)
    (ha : |a| ≤ (C * (M + 4 * M ^ 2) + 4 * M ^ 3) * s ^ 3)
    (hp : |p - μ * b| ≤ C * (M + 4 * M ^ 2) * s ^ 2) (hq : |q| ≤ C) (hC : 0 ≤ C)
    (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    |(p * b + q * a) / (a ^ 2 + b ^ 2) + 2 * (a ^ 2 - b ^ 2) - μ| ≤
      (4 * (C * (C * (M + 4 * M ^ 2) + 4 * M ^ 3) + C * (M + 4 * M ^ 2) * M +
      (C * (M + 4 * M ^ 2) + 4 * M ^ 3) ^ 2) / w0 ^ 2 +
      2 * (M ^ 2 + (C * (M + 4 * M ^ 2) + 4 * M ^ 3) ^ 2)) * s := by
  set K1 := C * (M + 4 * M ^ 2) with hK1
  set K2 := C * (M + 4 * M ^ 2) + 4 * M ^ 3 with hK2
  have hK1n : 0 ≤ K1 := by positivity
  have hK2n : 0 ≤ K2 := by positivity
  have hbpos : 0 < |b| := lt_of_lt_of_le (by positivity) hb1
  have hb2' : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
  have hP : 0 < a ^ 2 + b ^ 2 := by rw [hb2']; positivity
  have hPlow : (w0 / 2 * s) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hb1 2; rw [hb2']; nlinarith [sq_nonneg a]
  have e : (p * b + q * a) / (a ^ 2 + b ^ 2) + 2 * (a ^ 2 - b ^ 2) - μ =
      ((p - μ * b) * b + q * a - μ * a ^ 2) / (a ^ 2 + b ^ 2) + 2 * (a ^ 2 - b ^ 2) := by
    have hP' : a ^ 2 + b ^ 2 ≠ 0 := hP.ne'
    field_simp
    ring
  rw [e]
  have hs3 : s ^ 3 ≤ s ^ 2 := by nlinarith [sq_nonneg s]
  have hs6 : s ^ 6 ≤ s ^ 3 := by
    have : s ^ 3 ≤ 1 := pow_le_one₀ hs0.le hs1
    nlinarith [pow_pos hs0 3]
  have haa : a ^ 2 ≤ K2 ^ 2 * s ^ 6 := by
    have := sq_le_sq' (abs_le.1 ha).1 (abs_le.1 ha).2
    calc a ^ 2 ≤ (K2 * s ^ 3) ^ 2 := this
      _ = K2 ^ 2 * s ^ 6 := by ring
  have hnum : |(p - μ * b) * b + q * a - μ * a ^ 2| ≤ (C * K2 + K1 * M + K2 ^ 2) * s ^ 3 := by
    have t1 : |q * a| ≤ C * (K2 * s ^ 3) := by
      rw [abs_mul]; exact mul_le_mul hq ha (abs_nonneg _) hC
    have t2 : |(p - μ * b) * b| ≤ (K1 * s ^ 2) * (M * s) := by
      rw [abs_mul]; exact mul_le_mul hp hb2 (abs_nonneg _) (by positivity)
    have t3 : |μ * a ^ 2| ≤ K2 ^ 2 * s ^ 3 := by
      rw [abs_of_nonneg (by positivity)]
      calc μ * a ^ 2 ≤ 1 * (K2 ^ 2 * s ^ 6) := mul_le_mul hμ1 haa (sq_nonneg _) zero_le_one
        _ ≤ K2 ^ 2 * s ^ 3 := by nlinarith [sq_nonneg K2]
    calc |(p - μ * b) * b + q * a - μ * a ^ 2| ≤ |(p - μ * b) * b| + |q * a| + |μ * a ^ 2| := by
          refine le_trans (abs_sub _ _) ?_
          gcongr; exact abs_add_le _ _
      _ ≤ (K1 * s ^ 2) * (M * s) + C * (K2 * s ^ 3) + K2 ^ 2 * s ^ 3 := by gcongr
      _ = (C * K2 + K1 * M + K2 ^ 2) * s ^ 3 := by ring
  have hfrac : |((p - μ * b) * b + q * a - μ * a ^ 2) / (a ^ 2 + b ^ 2)| ≤
      4 * (C * K2 + K1 * M + K2 ^ 2) / w0 ^ 2 * s := by
    rw [abs_div, abs_of_pos hP, div_le_iff₀ hP]
    calc |(p - μ * b) * b + q * a - μ * a ^ 2| ≤ (C * K2 + K1 * M + K2 ^ 2) * s ^ 3 := hnum
      _ = 4 * (C * K2 + K1 * M + K2 ^ 2) / w0 ^ 2 * s * (w0 / 2 * s) ^ 2 := by
          field_simp; ring
      _ ≤ 4 * (C * K2 + K1 * M + K2 ^ 2) / w0 ^ 2 * s * (a ^ 2 + b ^ 2) := by
          gcongr
  have hsq : |2 * (a ^ 2 - b ^ 2)| ≤ 2 * (M ^ 2 + K2 ^ 2) * s := by
    have h1 : b ^ 2 ≤ M ^ 2 * s ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg b) hb2 2; rw [hb2']; nlinarith
    have h2 : s ^ 2 ≤ s := by nlinarith
    have h3 : a ^ 2 + b ^ 2 ≤ (M ^ 2 + K2 ^ 2) * s := by
      have x1 : M ^ 2 * s ^ 2 ≤ M ^ 2 * s := mul_le_mul_of_nonneg_left h2 (sq_nonneg M)
      have x2 : K2 ^ 2 * s ^ 6 ≤ K2 ^ 2 * s := by
        have : s ^ 6 ≤ s := le_trans hs6 (le_trans hs3 h2)
        exact mul_le_mul_of_nonneg_left this (sq_nonneg K2)
      have e2 : (M ^ 2 + K2 ^ 2) * s = M ^ 2 * s + K2 ^ 2 * s := by ring
      linarith
    have hb0 := sq_nonneg b
    have ha0' := sq_nonneg a
    rw [abs_le]; constructor <;> linarith
  calc |((p - μ * b) * b + q * a - μ * a ^ 2) / (a ^ 2 + b ^ 2) + 2 * (a ^ 2 - b ^ 2)|
      ≤ |((p - μ * b) * b + q * a - μ * a ^ 2) / (a ^ 2 + b ^ 2)| + |2 * (a ^ 2 - b ^ 2)| :=
        abs_add_le _ _
    _ ≤ 4 * (C * K2 + K1 * M + K2 ^ 2) / w0 ^ 2 * s + 2 * (M ^ 2 + K2 ^ 2) * s := by gcongr
    _ = _ := by ring

-- ===== Solutions.CM15 =====
lemma Vy_eq' (μ : ℝ) (s : Phase) :
    Vy μ s = (s 2 * s 1 + s 3 * s 0) / (s 0 ^ 2 + s 1 ^ 2) + 2 * (s 0 ^ 2 - s 1 ^ 2) - μ := rfl

set_option maxHeartbeats 4000000 in
/-- The collision orbit closing the near family arrives strictly inside the lower near
quadrant: its Levi-Civita collision velocity has `w₁ > 0 > w₂`. -/
theorem near_collision_strict (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (x : LeftEnergyState μ c) (T : ℝ) (hT : 0 < T)
    (hx1 : (x : Phase) 1 = 0) (hx2 : (x : Phase) 2 = 0) (hx0 : 0 < (x : Phase) 0)
    (hq : ∀ t ∈ Ioo (-T) 0,
      0 < relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0 ∧
      relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0)
    (hc0 : ((φ (-T) x : LeftEnergyState μ c) : Phase) 0 = 0)
    (hc1 : ((φ (-T) x : LeftEnergyState μ c) : Phase) 1 = 0) :
    0 < ((φ (-T) x : LeftEnergyState μ c) : Phase) 2 ∧
      ((φ (-T) x : LeftEnergyState μ c) : Phase) 3 < 0 := by
  obtain ⟨M, hM0, hM⟩ := vf_bound μ c hμ0 hμ1 hc
  obtain ⟨C, hC0, hC⟩ := coll_bounds μ c hμ0 hμ1 hc
  obtain ⟨x', hx'⟩ : ∃ x' : LeftEnergyState μ c, x' = φ (-T) x := ⟨_, rfl⟩
  rw [← hx'] at hc0 hc1 ⊢
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → Phase, γ = fun u => ((φ u x' : LeftEnergyState μ c) : Phase) :=
    ⟨_, rfl⟩
  have hγd : ∀ u, γ u = ((φ u x' : LeftEnergyState μ c) : Phase) := fun u => by rw [hγ]
  have hγt : ∀ u, γ u = ((φ (u - T) x : LeftEnergyState μ c) : Phase) := by
    intro u; rw [hγd, hx', ← Flow.map_add, ← sub_eq_add_neg]
  have hγ0 : γ 0 = (x' : Phase) := by rw [hγd]; simp
  obtain ⟨w0, hw0⟩ : ∃ w0, w0 = (x' : Phase) 2 := ⟨_, rfl⟩
  obtain ⟨w1, hw1⟩ : ∃ w1, w1 = (x' : Phase) 3 := ⟨_, rfl⟩
  rw [← hw0, ← hw1]
  have hspeed := collision_speed μ c _ x'.2 hc0 hc1
  rw [← hw0, ← hw1] at hspeed
  -- signs along the arc
  have hz0 : ∀ s ∈ Ioo 0 T, 0 < γ s 0 := by
    intro s hs
    rw [hγt]
    by_contra hneg
    push Not at hneg
    have hcont : ContinuousOn (fun u => ((φ u x : LeftEnergyState μ c) : Phase) 0) (Icc (s - T) 0) :=
      fun u _ => ((flow_coords' μ c φ hφ x u).1).continuousAt.continuousWithinAt
    have h0 : ((φ 0 x : LeftEnergyState μ c) : Phase) 0 = (x : Phase) 0 := by simp
    have hmem : (0:ℝ) ∈ Icc ((fun u => ((φ u x : LeftEnergyState μ c) : Phase) 0) (s - T))
        ((fun u => ((φ u x : LeftEnergyState μ c) : Phase) 0) 0) :=
      ⟨hneg, by simp only; rw [h0]; exact hx0.le⟩
    obtain ⟨u, hu, hu0⟩ := intermediate_value_Icc (by linarith [hs.2]) hcont hmem
    simp only at hu0
    have hu' : u ≠ 0 := by rintro rfl; rw [h0] at hu0; linarith
    have := (hq u ⟨by linarith [hu.1, hs.1], lt_of_le_of_ne hu.2 hu'⟩).1
    rw [(relPos_eq μ _).1, hu0] at this
    nlinarith [sq_nonneg (((φ u x : LeftEnergyState μ c) : Phase) 1)]
  have hq' : ∀ s ∈ Ioo 0 T, 0 < relativePosition μ (γ s) 0 ∧ relativePosition μ (γ s) 1 < 0 := by
    intro s hs; rw [hγt]; exact hq (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hz1 : ∀ s ∈ Ioo 0 T, γ s 1 < 0 := by
    intro s hs
    have h := (hq' s hs).2; rw [(relPos_eq μ _).2] at h
    have := hz0 s hs
    by_contra h'; push Not at h'; nlinarith
  have hz01 : ∀ s ∈ Ioo 0 T, 0 < γ s 0 + γ s 1 := by
    intro s hs
    have h := (hq' s hs).1; rw [(relPos_eq μ _).1] at h
    have := hz0 s hs; have := hz1 s hs
    have e : 2 * (γ s 0 ^ 2 - γ s 1 ^ 2) = 2 * (γ s 0 - γ s 1) * (γ s 0 + γ s 1) := by ring
    rw [e] at h
    by_contra h'; push Not at h'
    have : 0 < 2 * (γ s 0 - γ s 1) := by linarith
    nlinarith
  -- second order expansion at the collision
  have est : ∀ s, 0 ≤ s → |γ s 0 - w0 * s| ≤ 3 * M * s ^ 2 ∧ |γ s 1 - w1 * s| ≤ 3 * M * s ^ 2 := by
    intro s hs
    obtain ⟨-, -, -, -, e4, e5⟩ := flow_estimates μ c hμ0 hμ1 hc φ hφ M hM x' s s
      (by rw [abs_of_nonneg hs])
    rw [hc0, hc1, ← hw0, ← hγd] at e4
    rw [hc0, hc1, ← hw1, ← hγd] at e5
    simp only [abs_zero, sub_zero, zero_add] at e4 e5
    have e : (M * s + 2 * (M * s)) * s = 3 * M * s ^ 2 := by ring
    rw [e] at e4 e5
    exact ⟨e4, e5⟩
  have small : ∀ κ > 0, ∃ s ∈ Ioo 0 T, 3 * M * s ^ 2 < κ * s := by
    intro κ hκ
    refine ⟨min (T / 2) (κ / (6 * M)), ⟨by positivity, by
      have := min_le_left (T / 2) (κ / (6 * M)); linarith⟩, ?_⟩
    set s := min (T / 2) (κ / (6 * M))
    have hs : 0 < s := by positivity
    have hsκ : s ≤ κ / (6 * M) := min_le_right _ _
    have : 3 * M * s ≤ κ / 2 := by
      have := mul_le_mul_of_nonneg_left hsκ (by positivity : (0:ℝ) ≤ 3 * M)
      rw [show 3 * M * (κ / (6 * M)) = κ / 2 by field_simp; ring] at this; linarith
    nlinarith
  have hw0nn : 0 ≤ w0 := by
    by_contra h; push Not at h
    obtain ⟨s, hs, hsm⟩ := small (-w0) (by linarith)
    have := (abs_le.1 (est s hs.1.le).1).2
    have := hz0 s hs
    nlinarith
  have hw1np : w1 ≤ 0 := by
    by_contra h; push Not at h
    obtain ⟨s, hs, hsm⟩ := small w1 h
    have := (abs_le.1 (est s hs.1.le).2).1
    have := hz1 s hs
    nlinarith
  have hw01 : 0 ≤ w0 + w1 := by
    by_contra h; push Not at h
    obtain ⟨s, hs, hsm⟩ := small (-(w0 + w1) / 2) (by linarith)
    have := (abs_le.1 (est s hs.1.le).1).2
    have := (abs_le.1 (est s hs.1.le).2).2
    have := hz01 s hs
    nlinarith
  have hw0pos : 0 < w0 := by
    rcases eq_or_lt_of_le hw0nn with h | h
    · exfalso
      have : w1 = 0 := by linarith
      rw [← h, this] at hspeed; simp at hspeed; linarith
    · exact h
  refine ⟨hw0pos, lt_of_le_of_ne hw1np ?_⟩
  -- strictness: the collision velocity is not horizontal
  intro hw1z
  have hc3 : (x' : Phase) 3 = 0 := by rw [← hw1]; exact hw1z
  -- estimates near the collision
  set K1 := C * (M + 4 * M ^ 2)
  set K2 := C * (M + 4 * M ^ 2) + 4 * M ^ 3
  set Kv := 4 * (C * K2 + K1 * M + K2 ^ 2) / w0 ^ 2 + 2 * (M ^ 2 + K2 ^ 2) with hKv
  have hKv0 : 0 < Kv := by positivity
  set s1 := min (min 1 (T / 2)) (w0 / (6 * M)) with hs1def
  have hs1 : 0 < s1 := lt_min (lt_min one_pos (by linarith)) (by positivity)
  have hs1a : s1 ≤ 1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hs1b : s1 ≤ T / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hs1c : s1 ≤ w0 / (6 * M) := min_le_right _ _
  have hVy : ∀ s ∈ Ioc 0 s1, |Vy μ (γ s)| ≤ Kv * s := by
    intro s hs
    obtain ⟨cq, cb⟩ := coll_est_near μ c hμ0 hμ1 hc φ hφ M hM hM0 C hC x' hc0 hc1 hc3 s s
      (by rw [abs_of_pos hs.1]) (le_trans hs.2 hs1a)
    rw [← hγd] at cq cb
    obtain ⟨e0, -⟩ := est s hs.1.le
    have ha1 : w0 / 2 * s ≤ γ s 0 := by
      have h3 : 3 * M * s ≤ w0 / 2 := by
        have := mul_le_mul_of_nonneg_left (le_trans hs.2 hs1c) (by positivity : (0:ℝ) ≤ 3 * M)
        rw [show 3 * M * (w0 / (6 * M)) = w0 / 2 by field_simp; ring] at this; linarith
      have := (abs_le.1 e0).1
      nlinarith [hs.1]
    obtain ⟨f0, -⟩ := (flow_estimates μ c hμ0 hμ1 hc φ hφ M hM x' s s (by rw [abs_of_pos hs.1]))
    rw [hc0, sub_zero, ← hγd] at f0
    have ha2 : γ s 0 ≤ M * s := le_trans (le_abs_self _) f0
    have := Vy_small_near μ M C w0 s (γ s 0) (γ s 1) (γ s 2) (γ s 3) hM0 hw0pos hs.1
      (le_trans hs.2 hs1a) ha1 ha2 cb cq (by rw [hγd]; exact (hC _ (φ s x').2).2.2.1) hC0.le hμ0.le
      hμ1.le
    rw [Vy_eq']
    have e : γ s 2 * γ s 1 + γ s 3 * γ s 0 = γ s 2 * γ s 1 + γ s 3 * γ s 0 := rfl
    exact this
  -- `v₂` increases along the arc near the collision
  have hVx : ∀ s ∈ Ioo 0 T, 0 < Vx (γ s) := by
    intro s hs
    have hsT : s - T ∈ Ioo (-T) 0 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hq'' : ∀ t' ∈ Ioo (-(T - s)) 0,
        0 < relativePosition μ ((φ t' x : LeftEnergyState μ c) : Phase) 0 ∧
        relativePosition μ ((φ t' x : LeftEnergyState μ c) : Phase) 1 < 0 := by
      intro t' ht'
      exact hq t' ⟨by linarith [ht'.1, hs.1], ht'.2⟩
    have hend' : relativePosition μ ((φ (-(T - s)) x : LeftEnergyState μ c) : Phase) 1 < 0 := by
      rw [show -(T - s) = s - T by ring]; exact (hq (s - T) hsT).2
    have := (birkhoff_near_quadrant_monotone μ c hμ0 hμ1 hc φ hφ x (T - s) (by linarith [hs.2])
      hx1 hx2 hx0.ne' hq'' hend').2
    rw [show -(T - s) = s - T by ring, (jv_eq μ _).1] at this
    rw [hγt]; exact this
  have hPpos : ∀ s ∈ Ioo 0 T, 0 < zNormSq (γ s) := by
    intro s hs; unfold zNormSq; have := hz0 s hs; positivity
  have hVyd : ∀ s ∈ Ioo 0 T, HasDerivAt (fun u => Vy μ (γ u))
      (4 * zNormSq (γ s) * (2 * Vx (γ s) + Omy μ (γ s))) s := by
    intro s hs
    have := vy_hasDerivAt μ c φ hφ x' s (by rw [← hγd]; exact hPpos s hs)
    have hfun : (fun u => Vy μ (γ u)) = fun u => Vy μ ((φ u x' : LeftEnergyState μ c) : Phase) := by
      funext u; rw [hγd]
    rw [hfun, hγd]; exact this
  have hVymono : StrictMonoOn (fun u => Vy μ (γ u)) (Ioo 0 T) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
      (fun s hs => (hVyd s hs).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Ioo] at hs
    rw [(hVyd s hs).deriv]
    have hy : 4 * γ s 0 * γ s 1 < 0 := by
      have := (hq' s hs).2; rwa [(relPos_eq μ _).2] at this
    have := omega_y_pos μ c hμ0 hμ1 hc (γ s) (by rw [hγd]; exact (φ s x').2) hy
    have := hVx s hs
    have := hPpos s hs
    positivity
  have hVypos : ∀ s ∈ Ioo 0 s1, 0 < Vy μ (γ s) := by
    intro s hs
    by_contra hle; push Not at hle
    have hsT : s < T := by linarith [hs.2]
    set t0 := s / 2 with ht0def
    have ht0 : t0 ∈ Ioo 0 T := ⟨half_pos hs.1, by linarith [hs.1]⟩
    have hlt := hVymono ht0 ⟨hs.1, hsT⟩ (by linarith [hs.1])
    simp only at hlt
    set δ0 := -Vy μ (γ t0)
    have hδ0 : 0 < δ0 := by linarith
    set t' := min (t0 / 2) (δ0 / (2 * Kv))
    have ht'0 : 0 < t' := lt_min (half_pos ht0.1) (div_pos hδ0 (by positivity))
    have ht't0 : t' < t0 := lt_of_le_of_lt (min_le_left _ _) (by linarith [ht0.1])
    have h1 := hVymono ⟨ht'0, by linarith [ht0.2]⟩ ht0 ht't0
    simp only at h1
    have ht'le : t' ≤ t0 / 2 := min_le_left _ _
    have h2 := hVy t' ⟨ht'0, by linarith [hs.2, ht0.1]⟩
    have h3 : Kv * t' ≤ δ0 / 2 := by
      have := mul_le_mul_of_nonneg_left (min_le_right (t0 / 2) (δ0 / (2 * Kv))) hKv0.le
      rw [show Kv * (δ0 / (2 * Kv)) = δ0 / 2 by field_simp] at this; exact this
    have := (abs_le.1 h2).1
    linarith
  -- hence the height increases from the collision, contradicting `x₂ < 0`
  have hyd : ∀ s, HasDerivAt (fun u => relativePosition μ (γ u) 1) (Yd μ (γ s)) s := by
    intro s
    have hfun : (fun u => relativePosition μ (γ u) 1) =
        fun u => relativePosition μ ((φ u x' : LeftEnergyState μ c) : Phase) 1 := by
      funext u; rw [hγd]
    rw [hfun, hγd]; exact y_hasDerivAt μ c φ hφ x' s
  have hymono : StrictMonoOn (fun u => relativePosition μ (γ u) 1) (Icc 0 (s1 / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun s _ => (hyd s).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Icc] at hs
    rw [(hyd s).deriv]
    have hsT : s ∈ Ioo 0 T := ⟨hs.1, by linarith [hs.2]⟩
    have hP := hPpos s hsT
    rw [Yd_eq μ _ (by unfold zNormSq at hP; exact hP.ne')]
    have := hVypos s ⟨hs.1, by linarith [hs.2]⟩
    unfold zNormSq at hP
    positivity
  have := hymono ⟨le_refl _, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith : (0:ℝ) < s1 / 4)
  simp only at this
  have h0 : relativePosition μ (γ 0) 1 = 0 := by
    rw [(relPos_eq μ _).2, hγ0, hc0]; ring
  rw [h0] at this
  have := (hq' (s1 / 4) ⟨by linarith, by linarith⟩).2
  linarith

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (x : LeftEnergyState μ c) (T : ℝ) (hT : 0 < T)
    (hx1 : (x : Phase) 1 = 0) (hx2 : (x : Phase) 2 = 0) (hx0 : 0 < (x : Phase) 0)
    (hq : ∀ t ∈ Set.Ioo (-T) 0,
      0 < relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0 ∧
      relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0)
    (hc0 : ((φ (-T) x : LeftEnergyState μ c) : Phase) 0 = 0)
    (hc1 : ((φ (-T) x : LeftEnergyState μ c) : Phase) 1 = 0) :
    0 < ((φ (-T) x : LeftEnergyState μ c) : Phase) 2 ∧
      ((φ (-T) x : LeftEnergyState μ c) : Phase) 3 < 0 :=
  near_collision_strict μ c hμ0 hμ1 hc φ hφ x T hT hx1 hx2 hx0 hq hc0 hc1
