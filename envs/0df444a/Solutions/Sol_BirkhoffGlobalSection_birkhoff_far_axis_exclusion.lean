-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_far_axis_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T15:20:31.173979+00:00
-- url     : https://prove2.me/submissions/79dc1fe6-3731-4780-9265-a9c6ecb94beb

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

-- ===== Solutions.CM19 =====
set_option maxHeartbeats 4000000 in
/-- Boundary exclusion for near orbits. A backward orbit from a moving near-axis start that
stays in the closed lower-right quadrant without colliding either stays in the open
quadrant, or already contains a near shooting arc of shorter length. -/
theorem near_boundary_exclusion (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (x : LeftEnergyState μ c) (T : ℝ) (hT : 0 < T)
    (hx1 : (x : Phase) 1 = 0) (hx2 : (x : Phase) 2 = 0) (hx0 : 0 < (x : Phase) 0)
    (hv : 0 < Vy μ (x : Phase))
    (hcl : ∀ t ∈ Ioo (-T) 0,
      0 ≤ relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0 ∧
      relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 ≤ 0)
    (hP : ∀ t ∈ Ioo (-T) 0, 0 < zNormSq ((φ t x : LeftEnergyState μ c) : Phase)) :
    (∀ t ∈ Ioo (-T) 0,
      0 < relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0 ∧
      relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0) ∨
    ∃ τ, 0 < τ ∧ τ < T ∧ IsNearShootingArc φ x τ := by
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → Phase, γ = fun u => ((φ u x : LeftEnergyState μ c) : Phase) :=
    ⟨_, rfl⟩
  have hγd : ∀ u, γ u = ((φ u x : LeftEnergyState μ c) : Phase) := fun u => by rw [hγ]
  have hγ0 : γ 0 = (x : Phase) := by rw [hγd]; simp
  have hγc : Continuous γ := by
    rw [hγ]; exact continuous_subtype_val.comp (φ.continuous continuous_id continuous_const)
  set X : ℝ → ℝ := fun t => relativePosition μ (γ t) 0 with hX
  set Y : ℝ → ℝ := fun t => relativePosition μ (γ t) 1 with hY
  have hXc : Continuous X := (cont_relPos0 μ).comp hγc
  have hYc : Continuous Y := (cont_relPos1 μ).comp hγc
  have hcl' : ∀ t ∈ Ioo (-T) 0, 0 ≤ X t ∧ Y t ≤ 0 := by
    intro t ht; simp only [hX, hY, hγd]; exact hcl t ht
  have hP' : ∀ t ∈ Ioo (-T) 0, 0 < zNormSq (γ t) := by
    intro t ht; rw [hγd]; exact hP t ht
  have hYd : ∀ t, HasDerivAt Y (Yd μ (γ t)) t := by
    intro t
    have hfun : Y = fun v => relativePosition μ ((φ v x : LeftEnergyState μ c) : Phase) 1 := by
      funext v; simp only [hY, hγd]
    rw [hfun, hγd]; exact y_hasDerivAt μ c φ hφ x t
  have hVyd : ∀ t, 0 < zNormSq (γ t) → HasDerivAt (fun v => Vy μ (γ v))
      (4 * zNormSq (γ t) * (2 * Vx (γ t) + Omy μ (γ t))) t := by
    intro t ht
    have := vy_hasDerivAt μ c φ hφ x t (by rw [← hγd]; exact ht)
    have hfun : (fun v => Vy μ (γ v)) = fun v => Vy μ ((φ v x : LeftEnergyState μ c) : Phase) := by
      funext v; rw [hγd]
    rw [hfun, hγd]; exact this
  -- the orbit starts into the open quadrant
  have hP0 : (x : Phase) 0 ^ 2 + (x : Phase) 1 ^ 2 ≠ 0 := by positivity
  have hVyc : ContinuousAt (fun t => Vy μ (γ t)) 0 := by
    have := cont_Vy μ (x : Phase) hP0
    rw [← hγ0] at this
    exact this.comp hγc.continuousAt
  have hPc : ContinuousAt (fun t => zNormSq (γ t)) 0 := (cont_zNormSq.comp hγc).continuousAt
  have hX0 : 0 < X 0 := by
    simp only [hX]; rw [hγ0, (relPos_eq μ _).1, hx1]; have := hx0; nlinarith
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), 0 < Vy μ (γ t) ∧ 0 < zNormSq (γ t) ∧ 0 < X t := by
    refine (hVyc.eventually (Ioi_mem_nhds (by show 0 < Vy μ (γ 0); rw [hγ0]; exact hv))).and
      ((hPc.eventually (Ioi_mem_nhds ?_)).and (hXc.continuousAt.eventually (Ioi_mem_nhds hX0)))
    show 0 < zNormSq (γ 0); rw [hγ0]; unfold zNormSq; positivity
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set ε' := min (ε / 2) (T / 2) with hε'
  have hε'0 : 0 < ε' := lt_min (half_pos hε) (half_pos hT)
  have hε'1 : ε' < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hε'2 : ε' < T := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hT)
  have hin : ∀ t, -ε' ≤ t → t ≤ 0 → 0 < Vy μ (γ t) ∧ 0 < zNormSq (γ t) ∧ 0 < X t := by
    intro t h1 h2
    apply hball
    rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith
  have hYmono0 : StrictMonoOn Y (Icc (-ε') 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t _ => (hYd t).continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    rw [(hYd t).deriv]
    obtain ⟨h1, h2, -⟩ := hin t ht.1.le ht.2.le
    have hP2 := h2; unfold zNormSq at hP2
    rw [Yd_eq μ _ hP2.ne']
    unfold zNormSq at h2
    positivity
  have hY0 : Y 0 = 0 := by simp only [hY]; rw [hγ0, (relPos_eq μ _).2, hx1]; ring
  have hloc : ∀ t ∈ Ioo (-ε') 0, 0 < X t ∧ Y t < 0 := by
    intro t ht
    refine ⟨(hin t ht.1.le ht.2.le).2.2, ?_⟩
    have := hYmono0 ⟨ht.1.le, ht.2.le⟩ ⟨by linarith, le_refl _⟩ ht.2
    rwa [hY0] at this
  by_cases hall : ∀ t ∈ Ioo (-T) 0, 0 < X t ∧ Y t < 0
  · left; intro t ht; have := hall t ht; simp only [hX, hY, hγd] at this; exact this
  right
  push Not at hall
  obtain ⟨t1, ht1, hbad1⟩ := hall
  have hbad1' : X t1 * Y t1 = 0 := by
    obtain ⟨c1, c2⟩ := hcl' t1 ht1
    rcases eq_or_lt_of_le c1 with h | h
    · rw [← h]; ring
    · have := hbad1 h
      have : Y t1 = 0 := le_antisymm c2 this
      rw [this]; ring
  have ht1ε : t1 ≤ -ε' := by
    by_contra h; push Not at h
    have h2 := hloc t1 ⟨h, ht1.2⟩
    have h3 := hbad1 h2.1
    linarith [h2.2]
  -- the last boundary contact before the start
  set K := Icc t1 (-ε') ∩ {t | X t * Y t = 0} with hK
  have hKc : IsCompact K :=
    isCompact_Icc.inter_right (isClosed_eq (hXc.mul hYc) continuous_const)
  have hKne : K.Nonempty := ⟨t1, ⟨le_refl _, ht1ε⟩, hbad1'⟩
  obtain ⟨t0, ⟨ht0I, ht0f⟩, ht0max⟩ := hKc.exists_isGreatest hKne
  have ht0T : t0 ∈ Ioo (-T) 0 := ⟨by linarith [ht1.1, ht0I.1], by linarith [ht0I.2]⟩
  have hopen : ∀ t ∈ Ioo t0 0, 0 < X t ∧ Y t < 0 := by
    intro t ht
    by_cases htε : t ≤ -ε'
    · have htT : t ∈ Ioo (-T) 0 := ⟨by linarith [ht0T.1, ht.1], ht.2⟩
      have hnot : X t * Y t ≠ 0 := by
        intro h0
        have := ht0max ⟨⟨by linarith [ht0I.1, ht.1], htε⟩, h0⟩
        linarith [ht.1]
      obtain ⟨c1, c2⟩ := hcl' t htT
      have hX' : X t ≠ 0 := fun h => hnot (by rw [h]; ring)
      have hY' : Y t ≠ 0 := fun h => hnot (by rw [h]; ring)
      exact ⟨lt_of_le_of_ne c1 (Ne.symm hX'), lt_of_le_of_ne c2 hY'⟩
    · push Not at htε; exact hloc t ⟨htε, ht.2⟩
  obtain ⟨c1, c2⟩ := hcl' t0 ht0T
  rcases eq_or_lt_of_le c2 with hYt0 | hYt0
  · -- a contact with the axis: impossible
    exfalso
    have hVx : ∀ t ∈ Ioo t0 0, 0 < Vx (γ t) := by
      intro t ht
      have hq'' : ∀ t' ∈ Ioo (-(-t)) 0,
          0 < relativePosition μ ((φ t' x : LeftEnergyState μ c) : Phase) 0 ∧
          relativePosition μ ((φ t' x : LeftEnergyState μ c) : Phase) 1 < 0 := by
        intro t' ht'
        rw [neg_neg] at ht'
        have := hopen t' ⟨by linarith [ht.1, ht'.1], ht'.2⟩
        simp only [hX, hY, hγd] at this; exact this
      have hend' : relativePosition μ ((φ (-(-t)) x : LeftEnergyState μ c) : Phase) 1 < 0 := by
        rw [neg_neg]; have := (hopen t ht).2; simp only [hY, hγd] at this; exact this
      have := (birkhoff_near_quadrant_monotone μ c hμ0 hμ1 hc φ hφ x (-t) (by linarith [ht.2])
        hx1 hx2 hx0.ne' hq'' hend').2
      rw [neg_neg, (jv_eq μ _).1] at this
      rw [hγd]; exact this
    -- `v₂` vanishes at the contact, which is a local maximum of the height
    have hmax : IsLocalMax Y t0 := by
      filter_upwards [Ioo_mem_nhds ht0T.1 ht0T.2] with t ht
      rw [hYt0]; exact (hcl' t ht).2
    have hYd0 := hmax.hasDerivAt_eq_zero (hYd t0)
    have hPt0 := hP' t0 ht0T
    have hPt0' := hPt0; unfold zNormSq at hPt0'
    rw [Yd_eq μ _ hPt0'.ne'] at hYd0
    have hVy0 : Vy μ (γ t0) = 0 := by
      rcases mul_eq_zero.1 hYd0 with h | h
      · linarith
      · exact h
    set t2 := t0 / 2 with ht2
    have ht2I : t2 ∈ Ioo t0 0 := ⟨by linarith [ht0T.2], by linarith [ht0T.2]⟩
    have hVymono : StrictMonoOn (fun v => Vy μ (γ v)) (Icc t0 t2) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · intro t ht
        have htT : t ∈ Ioo (-T) 0 := ⟨by linarith [ht0T.1, ht.1], by linarith [ht.2, ht2I.2]⟩
        exact (hVyd t (hP' t htT)).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htI : t ∈ Ioo t0 0 := ⟨ht.1, by linarith [ht.2, ht2I.2]⟩
        have htT : t ∈ Ioo (-T) 0 := ⟨by linarith [ht0T.1, ht.1], htI.2⟩
        rw [(hVyd t (hP' t htT)).deriv]
        have hy : 4 * γ t 0 * γ t 1 < 0 := by
          have := (hopen t htI).2; simp only [hY] at this; rwa [(relPos_eq μ _).2] at this
        have := omega_y_pos μ c hμ0 hμ1 hc (γ t) (by rw [hγd]; exact (φ t x).2) hy
        have := hVx t htI
        have := hP' t htT
        positivity
    have hYmono : StrictMonoOn Y (Icc t0 t2) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
        (fun t _ => (hYd t).continuousAt.continuousWithinAt)
      intro t ht
      rw [interior_Icc] at ht
      have htT : t ∈ Ioo (-T) 0 := ⟨by linarith [ht0T.1, ht.1], by linarith [ht.2, ht2I.2]⟩
      rw [(hYd t).deriv]
      have hPt := hP' t htT
      unfold zNormSq at hPt
      rw [Yd_eq μ _ hPt.ne']
      have := hVymono ⟨le_refl _, by linarith [ht2I.1]⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
      simp only at this
      rw [hVy0] at this
      positivity
    have := hYmono ⟨le_refl _, by linarith [ht2I.1]⟩ ⟨ht2I.1.le, le_refl _⟩ ht2I.1
    linarith [(hopen t2 ht2I).2]
  · -- a crossing of the vertical line below the axis: a shorter near arc
    have hXt0 : X t0 = 0 := by
      rcases mul_eq_zero.1 ht0f with h | h
      · exact h
      · linarith
    refine ⟨-t0, by linarith [ht0T.2], by linarith [ht0T.1], by linarith [ht0T.2], ?_, ?_, ?_⟩
    · intro t ht
      rw [neg_neg] at ht
      have := hopen t ht; simp only [hX, hY, hγd] at this; exact this
    · rw [neg_neg]; simp only [hY, hγd] at hYt0; exact hYt0
    · rw [neg_neg]; simp only [hX, hγd] at hXt0; exact hXt0

set_option maxHeartbeats 4000000 in
/-- Axis-contact exclusion for far orbits. A forward orbit from a moving far-axis start that
stays in the closed lower half-plane with positive horizontal velocity and without colliding
stays strictly below the axis. -/
theorem far_axis_exclusion (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (x : LeftEnergyState μ c) (T : ℝ) (hT : 0 < T)
    (hx0 : (x : Phase) 0 = 0) (hx1 : 0 < (x : Phase) 1)
    (hv : Vy μ (x : Phase) < 0)
    (hcl : ∀ t ∈ Ioo 0 T, relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 ≤ 0)
    (hvx : ∀ t ∈ Ioo 0 T,
      0 < jacobiVelocity (leviCivitaToJacobi μ ((φ t x : LeftEnergyState μ c) : Phase)) 0)
    (hP : ∀ t ∈ Ioo 0 T, 0 < zNormSq ((φ t x : LeftEnergyState μ c) : Phase)) :
    ∀ t ∈ Ioo 0 T, relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0 := by
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → Phase, γ = fun u => ((φ u x : LeftEnergyState μ c) : Phase) :=
    ⟨_, rfl⟩
  have hγd : ∀ u, γ u = ((φ u x : LeftEnergyState μ c) : Phase) := fun u => by rw [hγ]
  have hγ0 : γ 0 = (x : Phase) := by rw [hγd]; simp
  have hγc : Continuous γ := by
    rw [hγ]; exact continuous_subtype_val.comp (φ.continuous continuous_id continuous_const)
  set Y : ℝ → ℝ := fun t => relativePosition μ (γ t) 1 with hY
  have hYc : Continuous Y := (cont_relPos1 μ).comp hγc
  have hcl' : ∀ t ∈ Ioo 0 T, Y t ≤ 0 := by
    intro t ht; simp only [hY, hγd]; exact hcl t ht
  have hP' : ∀ t ∈ Ioo 0 T, 0 < zNormSq (γ t) := by
    intro t ht; rw [hγd]; exact hP t ht
  have hVx : ∀ t ∈ Ioo 0 T, 0 < Vx (γ t) := by
    intro t ht; have := hvx t ht; rw [(jv_eq μ _).1] at this; rw [hγd]; exact this
  have hYd : ∀ t, HasDerivAt Y (Yd μ (γ t)) t := by
    intro t
    have hfun : Y = fun v => relativePosition μ ((φ v x : LeftEnergyState μ c) : Phase) 1 := by
      funext v; simp only [hY, hγd]
    rw [hfun, hγd]; exact y_hasDerivAt μ c φ hφ x t
  have hVyd : ∀ t, 0 < zNormSq (γ t) → HasDerivAt (fun v => Vy μ (γ v))
      (4 * zNormSq (γ t) * (2 * Vx (γ t) + Omy μ (γ t))) t := by
    intro t ht
    have := vy_hasDerivAt μ c φ hφ x t (by rw [← hγd]; exact ht)
    have hfun : (fun v => Vy μ (γ v)) = fun v => Vy μ ((φ v x : LeftEnergyState μ c) : Phase) := by
      funext v; rw [hγd]
    rw [hfun, hγd]; exact this
  -- the orbit starts below the axis
  have hP0 : (x : Phase) 0 ^ 2 + (x : Phase) 1 ^ 2 ≠ 0 := by positivity
  have hVyc : ContinuousAt (fun t => Vy μ (γ t)) 0 := by
    have := cont_Vy μ (x : Phase) hP0
    rw [← hγ0] at this
    exact this.comp hγc.continuousAt
  have hPc : ContinuousAt (fun t => zNormSq (γ t)) 0 := (cont_zNormSq.comp hγc).continuousAt
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), Vy μ (γ t) < 0 ∧ 0 < zNormSq (γ t) := by
    refine (hVyc.eventually (Iio_mem_nhds (by show Vy μ (γ 0) < 0; rw [hγ0]; exact hv))).and
      (hPc.eventually (Ioi_mem_nhds ?_))
    show 0 < zNormSq (γ 0); rw [hγ0]; unfold zNormSq; positivity
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set ε' := min (ε / 2) (T / 2) with hε'
  have hε'0 : 0 < ε' := lt_min (half_pos hε) (half_pos hT)
  have hε'1 : ε' < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hε'2 : ε' < T := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hT)
  have hin : ∀ t, 0 ≤ t → t ≤ ε' → Vy μ (γ t) < 0 ∧ 0 < zNormSq (γ t) := by
    intro t h1 h2
    apply hball
    rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith
  have hYanti0 : StrictAntiOn Y (Icc 0 ε') := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t _ => (hYd t).continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    rw [(hYd t).deriv]
    obtain ⟨h1, h2⟩ := hin t ht.1.le ht.2.le
    unfold zNormSq at h2
    rw [Yd_eq μ _ h2.ne']
    have : 0 < 4 * (γ t 0 ^ 2 + γ t 1 ^ 2) := by positivity
    nlinarith
  have hY0 : Y 0 = 0 := by simp only [hY]; rw [hγ0, (relPos_eq μ _).2, hx0]; ring
  have hloc : ∀ t ∈ Ioo 0 ε', Y t < 0 := by
    intro t ht
    have := hYanti0 ⟨le_refl _, hε'0.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
    rwa [hY0] at this
  by_contra hall
  push Not at hall
  obtain ⟨t1, ht1, hbad1⟩ := hall
  have hY1 : Y t1 = 0 := le_antisymm (hcl' t1 ht1) (by simp only [hY, hγd]; exact hbad1)
  have ht1ε : ε' ≤ t1 := by
    by_contra h; push Not at h
    have := hloc t1 ⟨ht1.1, h⟩; linarith
  -- the first contact with the axis
  set K := Icc ε' t1 ∩ {t | Y t = 0} with hK
  have hKc : IsCompact K := isCompact_Icc.inter_right (isClosed_eq hYc continuous_const)
  have hKne : K.Nonempty := ⟨t1, ⟨ht1ε, le_refl _⟩, hY1⟩
  obtain ⟨t0, ⟨ht0I, hYt0⟩, ht0min⟩ := hKc.exists_isLeast hKne
  have ht0T : t0 ∈ Ioo 0 T := ⟨by linarith [ht0I.1], by linarith [ht1.2, ht0I.2]⟩
  have hopen : ∀ t ∈ Ioo 0 t0, Y t < 0 := by
    intro t ht
    by_cases htε : ε' ≤ t
    · have htT : t ∈ Ioo 0 T := ⟨ht.1, by linarith [ht0T.2, ht.2]⟩
      have hnot : Y t ≠ 0 := by
        intro h0
        have := ht0min ⟨⟨htε, by linarith [ht0I.2, ht.2]⟩, h0⟩
        linarith [ht.2]
      exact lt_of_le_of_ne (hcl' t htT) hnot
    · push Not at htε; exact hloc t ⟨ht.1, htε⟩
  have hmax : IsLocalMax Y t0 := by
    filter_upwards [Ioo_mem_nhds ht0T.1 ht0T.2] with t ht
    rw [hYt0]; exact hcl' t ht
  have hYd0 := hmax.hasDerivAt_eq_zero (hYd t0)
  have hPt0 := hP' t0 ht0T
  have hPt0' := hPt0; unfold zNormSq at hPt0'
  rw [Yd_eq μ _ hPt0'.ne'] at hYd0
  have hVy0 : Vy μ (γ t0) = 0 := by
    rcases mul_eq_zero.1 hYd0 with h | h
    · linarith
    · exact h
  set t2 := t0 / 2 with ht2
  have ht2I : t2 ∈ Ioo 0 t0 := ⟨by linarith [ht0T.1], by linarith [ht0T.1]⟩
  have hVymono : StrictMonoOn (fun v => Vy μ (γ v)) (Icc t2 t0) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro t ht
      have htT : t ∈ Ioo 0 T := ⟨by linarith [ht2I.1, ht.1], by linarith [ht.2, ht0T.2]⟩
      exact (hVyd t (hP' t htT)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htI : t ∈ Ioo 0 t0 := ⟨by linarith [ht2I.1, ht.1], ht.2⟩
      have htT : t ∈ Ioo 0 T := ⟨htI.1, by linarith [ht.2, ht0T.2]⟩
      rw [(hVyd t (hP' t htT)).deriv]
      have hy : 4 * γ t 0 * γ t 1 < 0 := by
        have := hopen t htI; simp only [hY] at this; rwa [(relPos_eq μ _).2] at this
      have := omega_y_pos μ c hμ0 hμ1 hc (γ t) (by rw [hγd]; exact (φ t x).2) hy
      have := hVx t htT
      have := hP' t htT
      positivity
  have hYanti : StrictAntiOn Y (Icc t2 t0) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t _ => (hYd t).continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have htT : t ∈ Ioo 0 T := ⟨by linarith [ht2I.1, ht.1], by linarith [ht.2, ht0T.2]⟩
    rw [(hYd t).deriv]
    have hPt := hP' t htT
    unfold zNormSq at hPt
    rw [Yd_eq μ _ hPt.ne']
    have := hVymono ⟨ht.1.le, ht.2.le⟩ ⟨by linarith [ht2I.2], le_refl _⟩ ht.2
    simp only at this
    rw [hVy0] at this
    have : 0 < 4 * (γ t 0 ^ 2 + γ t 1 ^ 2) := by positivity
    nlinarith
  have := hYanti ⟨le_refl _, ht2I.2.le⟩ ⟨ht2I.2.le, le_refl _⟩ ht2I.2
  have h0 : Y t0 = 0 := hYt0
  linarith [hopen t2 ht2I]

/-- Two Levi-Civita coordinates with `x₁ = x₂ = 0` vanish. -/
lemma z_zero_of_pos_zero (a b : ℝ) (h1 : 2 * (a ^ 2 - b ^ 2) = 0) (h2 : 4 * a * b = 0) :
    a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    have : a ^ 4 = 0 := by nlinarith [sq_nonneg (a * b)]
    exact pow_eq_zero_iff (by norm_num) |>.1 this
  refine ⟨ha, ?_⟩
  rw [ha] at h1
  have : b ^ 2 = 0 := by linarith
  exact pow_eq_zero_iff (by norm_num) |>.1 this

/-- Near limit orbits: if a closed-quadrant, collision-free backward orbit from a moving
near start reaches the vertical line at time `-T` and no near arc exists from the start, then
the orbit is in the open quadrant on `(-T, 0)` and ends in a collision. -/
theorem near_limit_collision (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (x : LeftEnergyState μ c) (T : ℝ) (hT : 0 < T)
    (hx1 : (x : Phase) 1 = 0) (hx2 : (x : Phase) 2 = 0) (hx0 : 0 < (x : Phase) 0)
    (hv : 0 < Vy μ (x : Phase))
    (hcl : ∀ t ∈ Ioo (-T) 0,
      0 ≤ relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0 ∧
      relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 ≤ 0)
    (hP : ∀ t ∈ Ioo (-T) 0, 0 < zNormSq ((φ t x : LeftEnergyState μ c) : Phase))
    (hX : relativePosition μ ((φ (-T) x : LeftEnergyState μ c) : Phase) 0 = 0)
    (hY : relativePosition μ ((φ (-T) x : LeftEnergyState μ c) : Phase) 1 ≤ 0)
    (hno : ¬ ∃ τ, IsNearShootingArc φ x τ) :
    (∀ t ∈ Ioo (-T) 0,
      0 < relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0 ∧
      relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
    ((φ (-T) x : LeftEnergyState μ c) : Phase) 0 = 0 ∧
    ((φ (-T) x : LeftEnergyState μ c) : Phase) 1 = 0 := by
  rcases near_boundary_exclusion μ c hμ0 hμ1 hc φ hφ x T hT hx1 hx2 hx0 hv hcl hP with hopen | hshort
  · refine ⟨hopen, ?_⟩
    rcases eq_or_lt_of_le hY with h | h
    · rw [(relPos_eq μ _).1] at hX; rw [(relPos_eq μ _).2] at h
      exact z_zero_of_pos_zero _ _ hX h
    · exact absurd ⟨T, hT, hopen, h, hX⟩ hno
  · obtain ⟨τ, -, -, harc⟩ := hshort
    exact absurd ⟨τ, harc⟩ hno

/-- Far limit orbits: if a collision-free forward orbit from a moving far start stays in the
closed lower half-plane with positive horizontal velocity on `(0, T)`, reaches the vertical line
at time `T`, and no far arc exists from the start, then it stays strictly below the axis on
`(0, T)` and ends either in a collision or in a vertical tangency below the axis. -/
theorem far_limit_end (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (x : LeftEnergyState μ c) (T : ℝ) (hT : 0 < T)
    (hx0 : (x : Phase) 0 = 0) (hx1 : 0 < (x : Phase) 1)
    (hv : Vy μ (x : Phase) < 0)
    (hcl : ∀ t ∈ Ioo 0 T, relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 ≤ 0)
    (hvx : ∀ t ∈ Ioo 0 T,
      0 < jacobiVelocity (leviCivitaToJacobi μ ((φ t x : LeftEnergyState μ c) : Phase)) 0)
    (hP : ∀ t ∈ Ioo 0 T, 0 < zNormSq ((φ t x : LeftEnergyState μ c) : Phase))
    (hX : relativePosition μ ((φ T x : LeftEnergyState μ c) : Phase) 0 = 0)
    (hY : relativePosition μ ((φ T x : LeftEnergyState μ c) : Phase) 1 ≤ 0)
    (hVxT : 0 ≤ jacobiVelocity (leviCivitaToJacobi μ ((φ T x : LeftEnergyState μ c) : Phase)) 0)
    (hno : ¬ ∃ τ, IsFarShootingArc φ x τ) :
    (∀ t ∈ Ioo 0 T, relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
    ((((φ T x : LeftEnergyState μ c) : Phase) 0 = 0 ∧ ((φ T x : LeftEnergyState μ c) : Phase) 1 = 0) ∨
      (relativePosition μ ((φ T x : LeftEnergyState μ c) : Phase) 1 < 0 ∧
        jacobiVelocity (leviCivitaToJacobi μ ((φ T x : LeftEnergyState μ c) : Phase)) 0 = 0)) := by
  have hopen := far_axis_exclusion μ c hμ0 hμ1 hc φ hφ x T hT hx0 hx1 hv hcl hvx hP
  refine ⟨hopen, ?_⟩
  rcases eq_or_lt_of_le hY with h | h
  · left
    rw [(relPos_eq μ _).1] at hX; rw [(relPos_eq μ _).2] at h
    exact z_zero_of_pos_zero _ _ hX h
  · right
    refine ⟨h, ?_⟩
    rcases eq_or_lt_of_le hVxT with h' | h'
    · exact h'.symm
    · exfalso
      apply hno
      refine ⟨T, hT, hopen, h, hX, fun u hu => ?_⟩
      rcases eq_or_lt_of_le hu.2 with h'' | h''
      · rw [h'']; exact h'
      · exact hvx u ⟨hu.1, h''⟩

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (x : LeftEnergyState μ c) (T : ℝ) (hT : 0 < T)
    (hx0 : (x : Phase) 0 = 0) (hx1 : 0 < (x : Phase) 1)
    (hv : jacobiVelocity (leviCivitaToJacobi μ (x : Phase)) 1 < 0)
    (hcl : ∀ t ∈ Set.Ioo 0 T, relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 ≤ 0)
    (hvx : ∀ t ∈ Set.Ioo 0 T, 0 < jacobiVelocity (leviCivitaToJacobi μ ((φ t x : LeftEnergyState μ c) : Phase)) 0)
    (hP : ∀ t ∈ Set.Ioo 0 T, 0 < zNormSq ((φ t x : LeftEnergyState μ c) : Phase)) :
    ∀ t ∈ Set.Ioo 0 T, relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0 := by
  exact far_axis_exclusion μ c hμ0 hμ1 hc φ hφ x T hT hx0 hx1
    (by rw [← (jv_eq μ _).2]; exact hv) hcl hvx hP
