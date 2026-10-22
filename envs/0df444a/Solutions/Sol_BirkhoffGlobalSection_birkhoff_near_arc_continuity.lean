-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_near_arc_continuity
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T09:46:23.716804+00:00
-- url     : https://prove2.me/submissions/d8573789-1d0c-4679-9fa8-27f491bd8209

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



section Abstract

variable {X : Type*} [TopologicalSpace X]

/-- An eventual property near `(s₀, p₀)` holds on a product box. -/
lemma box_of_eventually (P : ℝ → X → Prop) (s₀ : ℝ) (p₀ : X)
    (h : ∀ᶠ q : ℝ × X in 𝓝 (s₀, p₀), P q.1 q.2) :
    ∃ a > 0, ∀ᶠ p in 𝓝 p₀, ∀ s ∈ Icc (s₀ - a) (s₀ + a), P s p := by
  rw [nhds_prod_eq, eventually_prod_iff] at h
  obtain ⟨pa, hpa, pb, hpb, hP⟩ := h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hpa
  refine ⟨ε / 2, by positivity, hpb.mono fun p hp s hs => hP (hball ?_) hp⟩
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2]

lemma eventually_lt_of_continuousAt (G : ℝ → X → ℝ) (s₀ : ℝ) (p₀ : X)
    (hc : ContinuousAt (uncurry G) (s₀, p₀)) (hneg : G s₀ p₀ < 0) :
    ∀ᶠ q : ℝ × X in 𝓝 (s₀, p₀), G q.1 q.2 < 0 :=
  hc.eventually (Iio_mem_nhds hneg)

lemma eventually_pos_of_continuousAt (G : ℝ → X → ℝ) (s₀ : ℝ) (p₀ : X)
    (hc : ContinuousAt (uncurry G) (s₀, p₀)) (hpos : 0 < G s₀ p₀) :
    ∀ᶠ q : ℝ × X in 𝓝 (s₀, p₀), 0 < G q.1 q.2 :=
  hc.eventually (Ioi_mem_nhds hpos)

/-- Persistence of a transversal first crossing. The crossing function `f` increases through
`0` at `τ₀`, and before that `f < 0`. The side conditions `h, k < 0` start from `0` with
negative slope and hold up to the crossing. All of this persists, with a crossing time
close to `τ₀`, for parameters close to `p₀`. -/
theorem transversal_crossing_persists (p₀ : X) (τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (f h k f' h' k' : ℝ → X → ℝ)
    (hfc : ∀ s, ContinuousAt (uncurry f) (s, p₀))
    (hhc : ∀ s ∈ Ioc 0 τ₀, ContinuousAt (uncurry h) (s, p₀))
    (hkc : ∀ s ∈ Ioc 0 τ₀, ContinuousAt (uncurry k) (s, p₀))
    (hf'd : ∀ᶠ q : ℝ × X in 𝓝 (τ₀, p₀), HasDerivAt (fun s => f s q.2) (f' q.1 q.2) q.1)
    (hf'c : ContinuousAt (uncurry f') (τ₀, p₀)) (hf'pos : 0 < f' τ₀ p₀)
    (hh'd : ∀ᶠ q : ℝ × X in 𝓝 (0, p₀), HasDerivAt (fun s => h s q.2) (h' q.1 q.2) q.1)
    (hh'c : ContinuousAt (uncurry h') (0, p₀)) (hh'neg : h' 0 p₀ < 0)
    (hk'd : ∀ᶠ q : ℝ × X in 𝓝 (0, p₀), HasDerivAt (fun s => k s q.2) (k' q.1 q.2) q.1)
    (hk'c : ContinuousAt (uncurry k') (0, p₀)) (hk'neg : k' 0 p₀ < 0)
    (hh0 : ∀ p, h 0 p = 0) (hk0 : ∀ p, k 0 p = 0)
    (hf0 : f τ₀ p₀ = 0) (hfneg : ∀ s ∈ Ico 0 τ₀, f s p₀ < 0)
    (hhneg : ∀ s ∈ Ioc 0 τ₀, h s p₀ < 0) (hkneg : ∀ s ∈ Ioc 0 τ₀, k s p₀ < 0) :
    ∀ a > 0, ∀ᶠ p in 𝓝 p₀, ∃ τ : ℝ, |τ - τ₀| < a ∧ 0 < τ ∧ f τ p = 0 ∧
      (∀ s ∈ Ico 0 τ, f s p < 0) ∧ (∀ s ∈ Ioc 0 τ, h s p < 0 ∧ k s p < 0) := by
  intro a ha
  -- box around the crossing: derivative positive
  obtain ⟨a1, ha1, E1⟩ := box_of_eventually
    (fun s p => HasDerivAt (fun s => f s p) (f' s p) s ∧ 0 < f' s p) τ₀ p₀
    (hf'd.and (eventually_pos_of_continuousAt f' τ₀ p₀ hf'c hf'pos))
  -- box around the start
  obtain ⟨a2, ha2, E2⟩ := box_of_eventually
    (fun s p => HasDerivAt (fun s => h s p) (h' s p) s ∧ h' s p < 0 ∧
      HasDerivAt (fun s => k s p) (k' s p) s ∧ k' s p < 0 ∧ f s p < 0) 0 p₀
    (hh'd.and ((eventually_lt_of_continuousAt h' 0 p₀ hh'c hh'neg).and
      (hk'd.and ((eventually_lt_of_continuousAt k' 0 p₀ hk'c hk'neg).and
        (eventually_lt_of_continuousAt f 0 p₀ (hfc 0)
          (hfneg 0 ⟨le_refl _, hτ₀⟩))))))
  -- box around the crossing: side conditions
  obtain ⟨a3, ha3, E3⟩ := box_of_eventually (fun s p => h s p < 0 ∧ k s p < 0) τ₀ p₀
    ((eventually_lt_of_continuousAt h τ₀ p₀ (hhc τ₀ ⟨hτ₀, le_refl _⟩)
      (hhneg τ₀ ⟨hτ₀, le_refl _⟩)).and
     (eventually_lt_of_continuousAt k τ₀ p₀ (hkc τ₀ ⟨hτ₀, le_refl _⟩)
      (hkneg τ₀ ⟨hτ₀, le_refl _⟩)))
  set e := min a2 (τ₀ / 4) with he
  set w := min (min a (τ₀ / 4)) (min a1 a3) with hw
  have he0 : 0 < e := lt_min ha2 (by linarith)
  have hw0 : 0 < w := lt_min (lt_min ha (by linarith)) (lt_min ha1 ha3)
  have hea2 : e ≤ a2 := min_le_left _ _
  have heτ : e ≤ τ₀ / 4 := min_le_right _ _
  have hwa : w ≤ a := le_trans (min_le_left _ _) (min_le_left _ _)
  have hwτ : w ≤ τ₀ / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hwa1 : w ≤ a1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hwa3 : w ≤ a3 := le_trans (min_le_right _ _) (min_le_right _ _)
  -- values at the window ends for p₀
  have hwin0 := E1.self_of_nhds
  have hmono0 : StrictMonoOn (fun s => f s p₀) (Icc (τ₀ - w) (τ₀ + w)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro s hs
      exact ((hwin0 s ⟨by linarith [hs.1], by linarith [hs.2]⟩).1).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have := hwin0 s ⟨by linarith [hs.1], by linarith [hs.2]⟩
      rw [this.1.deriv]; exact this.2
  have hleft0 : f (τ₀ - w) p₀ < 0 := hfneg _ ⟨by linarith, by linarith⟩
  have hright0 : 0 < f (τ₀ + w) p₀ := by
    rw [← hf0]
    exact hmono0 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have Eleft : ∀ᶠ p in 𝓝 p₀, f (τ₀ - w) p < 0 :=
    (ContinuousAt.comp (x := p₀) (hfc (τ₀ - w)) (Continuous.prodMk_right (τ₀ - w)).continuousAt).eventually (Iio_mem_nhds hleft0)
  have Eright : ∀ᶠ p in 𝓝 p₀, 0 < f (τ₀ + w) p :=
    (ContinuousAt.comp (x := p₀) (hfc (τ₀ + w)) (Continuous.prodMk_right (τ₀ + w)).continuousAt).eventually (Ioi_mem_nhds hright0)
  -- the middle compact interval
  have Emid : ∀ᶠ p in 𝓝 p₀, ∀ s ∈ Icc e (τ₀ - w), f s p < 0 ∧ h s p < 0 ∧ k s p < 0 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hs1 : s < τ₀ := by linarith [hs.2]
    have cf : ContinuousAt (uncurry f ∘ Prod.swap) (p₀, s) :=
      ContinuousAt.comp (x := (p₀, s)) (hfc s) continuous_swap.continuousAt
    have ch : ContinuousAt (uncurry h ∘ Prod.swap) (p₀, s) :=
      ContinuousAt.comp (x := (p₀, s)) (hhc s ⟨hs0, hs1.le⟩) continuous_swap.continuousAt
    have ck : ContinuousAt (uncurry k ∘ Prod.swap) (p₀, s) :=
      ContinuousAt.comp (x := (p₀, s)) (hkc s ⟨hs0, hs1.le⟩) continuous_swap.continuousAt
    exact (cf.eventually (Iio_mem_nhds (hfneg s ⟨hs0.le, hs1⟩))).and
      ((ch.eventually (Iio_mem_nhds (hhneg s ⟨hs0, hs1.le⟩))).and
        (ck.eventually (Iio_mem_nhds (hkneg s ⟨hs0, hs1.le⟩))))
  filter_upwards [E1, E2, E3, Eleft, Eright, Emid] with p h1 h2 h3 hl hr hm
  -- the crossing for p
  have hcont : ContinuousOn (fun s => f s p) (Icc (τ₀ - w) (τ₀ + w)) := fun s hs =>
    (h1 s ⟨by linarith [hs.1], by linarith [hs.2]⟩).1.continuousAt.continuousWithinAt
  have hmono : StrictMonoOn (fun s => f s p) (Icc (τ₀ - w) (τ₀ + w)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
    intro s hs
    rw [interior_Icc] at hs
    have := h1 s ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [this.1.deriv]; exact this.2
  obtain ⟨τ, hτ, hfτ⟩ := intermediate_value_Ioo (by linarith) hcont ⟨hl, hr⟩
  have hτa : |τ - τ₀| < a := by rw [abs_lt]; constructor <;> linarith [hτ.1, hτ.2]
  -- the side conditions near the start, via the mean value theorem
  have hstart : ∀ s ∈ Ioc 0 e, h s p < 0 ∧ k s p < 0 := by
    intro s hs
    have hbox : ∀ u ∈ Icc 0 s, u ∈ Icc (0 - a2) (0 + a2) := fun u hu =>
      ⟨by linarith [hu.1], by linarith [hu.2, hs.2]⟩
    constructor
    · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun u => h u p) (fun u => h' u p)
        hs.1 (fun u hu => (h2 u (hbox u hu)).1.continuousAt.continuousWithinAt)
        (fun u hu => (h2 u (hbox u (Ioo_subset_Icc_self hu))).1)
      have hneg := (h2 ξ (hbox ξ (Ioo_subset_Icc_self hξ))).2.1
      rw [hslope, hh0, sub_zero, sub_zero] at hneg
      exact (div_neg_iff.1 hneg).elim (fun h => absurd h.2 (not_lt.2 hs.1.le))
        (fun h => h.1)
    · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun u => k u p) (fun u => k' u p)
        hs.1 (fun u hu => (h2 u (hbox u hu)).2.2.1.continuousAt.continuousWithinAt)
        (fun u hu => (h2 u (hbox u (Ioo_subset_Icc_self hu))).2.2.1)
      have hneg := (h2 ξ (hbox ξ (Ioo_subset_Icc_self hξ))).2.2.2.1
      rw [hslope, hk0, sub_zero, sub_zero] at hneg
      exact (div_neg_iff.1 hneg).elim (fun h => absurd h.2 (not_lt.2 hs.1.le))
        (fun h => h.1)
  refine ⟨τ, hτa, by linarith [hτ.1], hfτ, ?_, ?_⟩
  · intro s hs
    rcases le_or_gt s e with h' | h'
    · exact (h2 s ⟨by linarith [hs.1], by linarith⟩).2.2.2.2
    rcases le_or_gt s (τ₀ - w) with h'' | h''
    · exact (hm s ⟨h'.le, h''⟩).1
    · rw [← hfτ]
      exact hmono ⟨h''.le, by linarith [hs.2, hτ.2]⟩ ⟨by linarith [hτ.1], hτ.2.le⟩ hs.2
  · intro s hs
    rcases le_or_gt s e with h' | h'
    · exact hstart s ⟨hs.1, h'⟩
    rcases le_or_gt s (τ₀ - w) with h'' | h''
    · exact ⟨(hm s ⟨h'.le, h''⟩).2.1, (hm s ⟨h'.le, h''⟩).2.2⟩
    · exact h3 s ⟨by linarith, by linarith [hs.2, hτ.2]⟩

end Abstract



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



lemma hasDerivAt_comp_neg' {g : ℝ → ℝ} {g' x : ℝ} (h : HasDerivAt g g' (-x)) :
    HasDerivAt (fun s => g (-s)) (-g') x := by
  have := h.comp x (hasDerivAt_neg x)
  simpa [Function.comp_def] using this

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (x₀ : LeftEnergyState μ c) (τ₀ : ℝ)
    (hx₀ : (x₀ : Phase) = nearShootingStart μ c r₀) (harc : IsNearShootingArc φ x₀ τ₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ r : ℝ, |r - r₀| < δ →
      ∃ x : LeftEnergyState μ c, (x : Phase) = nearShootingStart μ c r ∧ ∃ τ : ℝ,
        IsNearShootingArc φ x τ ∧
        dist (shootingCoordinates μ ((φ (-τ) x : LeftEnergyState μ c) : Phase))
          (shootingCoordinates μ ((φ (-τ₀) x₀ : LeftEnergyState μ c) : Phase)) < ε := by
  intro ε hε
  have hc0 : (x₀ : Phase) 0 = r₀ := by rw [hx₀]; simp [nearShootingStart]
  have hc1 : (x₀ : Phase) 1 = 0 := by rw [hx₀]; simp [nearShootingStart]
  have hc2 : (x₀ : Phase) 2 = 0 := by rw [hx₀]; simp [nearShootingStart]
  have hVy := near_arc_Vy_pos μ c hμ0 hμ1 hc φ hφ x₀ τ₀ hc1 hc2 (by rw [hc0]; exact hr₀.ne') harc
  rw [hx₀, nearStart_Vy μ c r₀ hr₀.ne'] at hVy
  have hR : 0 < nearR μ c r₀ := Real.sqrt_pos.1 ((div_pos_iff_of_pos_right hr₀).1 hVy)
  have hrad : 2 * r₀ ^ 2 < 1 := by
    have := comp_radius μ c hμ0 hμ1 hc _ x₀.2
    rw [hc0, hc1] at this
    nlinarith [sq_nonneg r₀]
  -- nearby starts lie on the component
  have hev : ∀ᶠ r in 𝓝 r₀, 0 < nearR μ c r ∧ 2 * r ^ 2 < 1 :=
    ((nearR_continuousAt μ c r₀ hrad.ne).eventually (Ioi_mem_nhds hR)).and
      ((by fun_prop : Continuous fun r : ℝ => 2 * r ^ 2).continuousAt.eventually (Iio_mem_nhds hrad))
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hmem : ∀ᶠ r in 𝓝 r₀, nearShootingStart μ c r ∈ leftEnergyComponent μ c := by
    filter_upwards [Metric.ball_mem_nhds r₀ hδ₁] with r hr
    have hsub : ∀ r' ∈ uIcc r₀ r, dist r' r₀ < δ₁ := fun r' hr' =>
      lt_of_le_of_lt (by rw [Real.dist_eq, Real.dist_eq]; exact abs_sub_left_of_mem_uIcc hr') hr
    apply mem_comp_of_path μ c (nearShootingStart μ c) r₀ r
    · intro r' hr'
      exact (nearStart_continuousAt μ c r' (hball (hsub r' hr')).2.ne).continuousWithinAt
    · intro r' hr'
      obtain ⟨h1, h2⟩ := hball (hsub r' hr')
      refine ⟨nearStart_K μ c r' h1.le, ?_⟩
      rw [nearStart_D]; nlinarith
    · rw [← hx₀]; exact x₀.2
  obtain ⟨Sx, hSx0, hSxc, hSxev, hSxall⟩ := start_family (nearShootingStart μ c) x₀ r₀ hx₀
    (nearStart_continuousAt μ c r₀ hrad.ne) hmem
  -- the functions of the abstract crossing lemma (time reversed)
  set Φ : ℝ → ℝ → Phase := fun s r => ((φ (-s) (Sx r) : LeftEnergyState μ c) : Phase) with hΦdef
  have hΦ : ∀ s, ContinuousAt (uncurry Φ) (s, r₀) := by
    intro s
    have := flow_state_continuousAt φ Sx r₀ hSxc (-1) s
    have e : uncurry Φ = fun q : ℝ × ℝ => ((φ ((-1) * q.1) (Sx q.2) : LeftEnergyState μ c) : Phase) := by
      funext q; simp [hΦdef, uncurry]
    rw [e]; exact this
  have hΦ0 : ∀ s, Φ s r₀ = ((φ (-s) x₀ : LeftEnergyState μ c) : Phase) := by
    intro s; simp [hΦdef, hSx0]
  set f : ℝ → ℝ → ℝ := fun s r => -relativePosition μ (Φ s r) 0 with hf
  set h : ℝ → ℝ → ℝ := fun s r => relativePosition μ (Φ s r) 1 with hh
  set f' : ℝ → ℝ → ℝ := fun s r => XRd (Φ s r) with hf'
  set h' : ℝ → ℝ → ℝ := fun s r => -Yd μ (Φ s r) with hh'
  have hderf : ∀ s r, HasDerivAt (fun s => f s r) (f' s r) s := by
    intro s r
    have h1 := (hasDerivAt_comp_neg' (xrel_hasDerivAt' μ c φ hφ (Sx r) (-s))).neg
    exact h1.congr_deriv (neg_neg _)
  have hderh : ∀ s r, HasDerivAt (fun s => h s r) (h' s r) s := by
    intro s r
    exact hasDerivAt_comp_neg' (y_hasDerivAt μ c φ hφ (Sx r) (-s))
  obtain ⟨hτ₀, hq, hend, hcross⟩ := harc
  -- data at the crossing and at the start
  have hmono := birkhoff_near_quadrant_monotone μ c hμ0 hμ1 hc φ hφ x₀ τ₀ hτ₀ hc1 hc2
    (by rw [hc0]; exact hr₀.ne') hq hend
  have hPcross : (φ (-τ₀) x₀ : Phase) 0 ^ 2 + (φ (-τ₀) x₀ : Phase) 1 ^ 2 ≠ 0 := by
    have := hend; rw [(relPos_eq μ _).2] at this
    have h0 : (φ (-τ₀) x₀ : Phase) 0 ≠ 0 := by rintro h0; rw [h0] at this; simp at this
    positivity
  have hVxcross : 0 < Vx ((φ (-τ₀) x₀ : LeftEnergyState μ c) : Phase) := by
    have := hmono.2; rwa [(jv_eq μ _).1] at this
  have hf'pos : 0 < f' τ₀ r₀ := by
    simp only [hf', hΦ0]
    rw [XRd_eq _ hPcross]
    have : 0 < (φ (-τ₀) x₀ : Phase) 0 ^ 2 + (φ (-τ₀) x₀ : Phase) 1 ^ 2 := by positivity
    positivity
  have hP0 : (x₀ : Phase) 0 ^ 2 + (x₀ : Phase) 1 ^ 2 ≠ 0 := by rw [hc0]; positivity
  have hh'neg : h' 0 r₀ < 0 := by
    simp only [hh', hΦ0, neg_zero, Flow.map_zero_apply]
    rw [Yd_eq μ _ hP0, hx₀, nearStart_Vy μ c r₀ hr₀.ne', ← hx₀]
    have : 0 < (x₀ : Phase) 0 ^ 2 + (x₀ : Phase) 1 ^ 2 := by rw [hc0]; positivity
    have : 0 < Real.sqrt (nearR μ c r₀) / r₀ := div_pos (Real.sqrt_pos.2 hR) hr₀
    nlinarith
  have hh0 : ∀ r, h 0 r = 0 := by
    intro r
    simp only [hh, hΦdef, neg_zero, Flow.map_zero_apply, (relPos_eq μ _).2]
    rcases hSxall r with e | e
    · rw [e]; simp [nearShootingStart]
    · rw [e, hc1]; ring
  have hf0 : f τ₀ r₀ = 0 := by simp only [hf, hΦ0, hcross, neg_zero]
  have hfneg : ∀ s ∈ Ico 0 τ₀, f s r₀ < 0 := by
    intro s hs
    simp only [hf, hΦ0]
    rcases eq_or_lt_of_le hs.1 with e | e
    · subst e
      simp only [neg_zero, Flow.map_zero_apply, (relPos_eq μ _).1, hc0, hc1]
      nlinarith
    · have := (hq (-s) ⟨by linarith [hs.2], by linarith⟩).1
      linarith
  have hhneg : ∀ s ∈ Ioc 0 τ₀, h s r₀ < 0 := by
    intro s hs
    simp only [hh, hΦ0]
    rcases eq_or_lt_of_le hs.2 with e | e
    · subst e; exact hend
    · exact (hq (-s) ⟨by linarith, by linarith [hs.1]⟩).2
  have hfc : ∀ s, ContinuousAt (uncurry f) (s, r₀) := fun s =>
    ((cont_relPos0 μ).continuousAt.comp (hΦ s)).neg
  have hhc : ∀ s, ContinuousAt (uncurry h) (s, r₀) := fun s =>
    (cont_relPos1 μ).continuousAt.comp (hΦ s)
  have hf'c : ContinuousAt (uncurry f') (τ₀, r₀) := cont_XRd.continuousAt.comp (hΦ τ₀)
  have hh'c : ContinuousAt (uncurry h') (0, r₀) := ((cont_Yd μ).continuousAt.comp (hΦ 0)).neg
  -- continuity of the crossing coordinates
  have hC : ContinuousAt (fun q : ℝ × ℝ => shootingCoordinates μ (Φ q.1 q.2)) (τ₀, r₀) := by
    have := cont_coords μ (Φ τ₀ r₀) (by rw [hΦ0]; exact hPcross) (by rw [hΦ0]; exact hVxcross.ne')
    exact ContinuousAt.comp (x := (τ₀, r₀)) this (hΦ τ₀)
  obtain ⟨a, ha, Ebox⟩ := box_of_eventually
    (fun s r => dist (shootingCoordinates μ (Φ s r)) (shootingCoordinates μ (Φ τ₀ r₀)) < ε)
    τ₀ r₀ (hC.eventually (Metric.ball_mem_nhds _ hε))
  have Ecross := transversal_crossing_persists r₀ τ₀ hτ₀ f h h f' h' h'
    (fun s => hfc s) (fun s _ => hhc s) (fun s _ => hhc s)
    (Eventually.of_forall fun q => hderf q.1 q.2) hf'c hf'pos
    (Eventually.of_forall fun q => hderh q.1 q.2) hh'c hh'neg
    (Eventually.of_forall fun q => hderh q.1 q.2) hh'c hh'neg
    hh0 hh0 hf0 hfneg hhneg hhneg a ha
  obtain ⟨δ, hδ, hfinal⟩ := Metric.eventually_nhds_iff.1 ((Ecross.and Ebox).and hSxev)
  refine ⟨δ, hδ, fun r hr => ?_⟩
  obtain ⟨⟨⟨τ, hτa, hτ, hfτ, hfbefore, hhbefore⟩, hbox⟩, hSr⟩ :=
    hfinal (by rwa [Real.dist_eq])
  refine ⟨Sx r, hSr, τ, ⟨hτ, ?_, ?_, ?_⟩, ?_⟩
  · intro t ht
    have h1 := hfbefore (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h2 := (hhbefore (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).1
    simp only [hf, hh, hΦdef, neg_neg] at h1 h2
    exact ⟨by linarith, h2⟩
  · have := (hhbefore τ ⟨hτ, le_refl _⟩).1
    simpa [hh, hΦdef] using this
  · have := hfτ
    simp only [hf, hΦdef] at this
    linarith
  · have := hbox τ ⟨by linarith [(abs_lt.1 hτa).1], by linarith [(abs_lt.1 hτa).2]⟩
    simpa [hΦdef, hSx0] using this



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


attribute [local irreducible] Omx Vy Vx zNormSq in
theorem far_arc_continuity (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (x₀ : LeftEnergyState μ c) (τ₀ : ℝ)
    (hx₀ : (x₀ : Phase) = farShootingStart μ c r₀) (harc : IsFarShootingArc φ x₀ τ₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ r : ℝ, |r - r₀| < δ →
      ∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c r ∧ ∃ τ : ℝ,
        IsFarShootingArc φ x τ ∧
        dist (shootingCoordinates μ ((φ τ x : LeftEnergyState μ c) : Phase))
          (shootingCoordinates μ ((φ τ₀ x₀ : LeftEnergyState μ c) : Phase)) < ε := by
  intro ε hε
  have hc0 : (x₀ : Phase) 0 = 0 := by rw [hx₀]; simp [farShootingStart]
  have hc1 : (x₀ : Phase) 1 = r₀ := by rw [hx₀]; simp [farShootingStart]
  have hc3 : (x₀ : Phase) 3 = 0 := by rw [hx₀]; simp [farShootingStart]
  have harc' := harc
  have hVy := far_arc_Vy_neg μ c hμ0 hμ1 hc φ hφ x₀ τ₀ hc0 (by rw [hc1]; exact hr₀.ne') harc
  have hVy' := hVy
  rw [hx₀, farStart_Vy μ c r₀ hr₀.ne'] at hVy'
  have hR : 0 < farR μ c r₀ := by
    have : 0 < Real.sqrt (farR μ c r₀) / r₀ := by linarith
    exact Real.sqrt_pos.1 ((div_pos_iff_of_pos_right hr₀).1 this)
  -- nearby starts lie on the component
  have hev : ∀ᶠ r in 𝓝 r₀, 0 < farR μ c r :=
    (farR_continuous μ c).continuousAt.eventually (Ioi_mem_nhds hR)
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hmem : ∀ᶠ r in 𝓝 r₀, farShootingStart μ c r ∈ leftEnergyComponent μ c := by
    filter_upwards [Metric.ball_mem_nhds r₀ hδ₁] with r hr
    have hsub : ∀ r' ∈ uIcc r₀ r, dist r' r₀ < δ₁ := fun r' hr' =>
      lt_of_le_of_lt (by rw [Real.dist_eq, Real.dist_eq]; exact abs_sub_left_of_mem_uIcc hr') hr
    apply mem_comp_of_path μ c (farShootingStart μ c) r₀ r
    · exact (farStart_continuous μ c).continuousOn
    · intro r' hr'
      refine ⟨farStart_K μ c r' (hball (hsub r' hr')).le, ?_⟩
      rw [farStart_D]; positivity
    · rw [← hx₀]; exact x₀.2
  obtain ⟨Sx, hSx0, hSxc, hSxev, hSxall⟩ := start_family (farShootingStart μ c) x₀ r₀ hx₀
    (farStart_continuous μ c).continuousAt hmem
  set Φ : ℝ → ℝ → Phase := fun s r => ((φ s (Sx r) : LeftEnergyState μ c) : Phase) with hΦdef
  have hΦ : ∀ s, ContinuousAt (uncurry Φ) (s, r₀) := by
    intro s
    have := flow_state_continuousAt φ Sx r₀ hSxc 1 s
    have e : uncurry Φ = fun q : ℝ × ℝ => ((φ (1 * q.1) (Sx q.2) : LeftEnergyState μ c) : Phase) := by
      funext q; simp [hΦdef, uncurry]
    rw [e]; exact this
  have hΦ0 : ∀ s, Φ s r₀ = ((φ s x₀ : LeftEnergyState μ c) : Phase) := by
    intro s; simp [hΦdef, hSx0]
  set f : ℝ → ℝ → ℝ := fun s r => relativePosition μ (Φ s r) 0 with hf
  set h : ℝ → ℝ → ℝ := fun s r => relativePosition μ (Φ s r) 1 with hh
  set k : ℝ → ℝ → ℝ := fun s r => -Vx (Φ s r) with hk
  set f' : ℝ → ℝ → ℝ := fun s r => XRd (Φ s r) with hf'
  set h' : ℝ → ℝ → ℝ := fun s r => Yd μ (Φ s r) with hh'
  set k' : ℝ → ℝ → ℝ := fun s r =>
    -(4 * zNormSq (Φ s r) * (Omx μ (Φ s r) - 2 * Vy μ (Φ s r))) with hk'
  have hderf : ∀ s r, HasDerivAt (fun s => f s r) (f' s r) s := fun s r =>
    xrel_hasDerivAt' μ c φ hφ (Sx r) s
  have hderh : ∀ s r, HasDerivAt (fun s => h s r) (h' s r) s := fun s r =>
    y_hasDerivAt μ c φ hφ (Sx r) s
  obtain ⟨hτ₀, hlow, hend, hcross, hv⟩ := harc
  have hP0 : (x₀ : Phase) 0 ^ 2 + (x₀ : Phase) 1 ^ 2 ≠ 0 := by rw [hc1]; positivity
  have hzP : ContinuousAt (fun q : ℝ × ℝ => zNormSq (Φ q.1 q.2)) (0, r₀) :=
    cont_zNormSq.continuousAt.comp (hΦ 0)
  have hPpos0 : 0 < zNormSq (Φ 0 r₀) := by
    rw [hΦ0]; simp only [Flow.map_zero_apply, zNormSq, hc1]; positivity
  have hderk : ∀ᶠ q : ℝ × ℝ in 𝓝 (0, r₀), HasDerivAt (fun s => k s q.2) (k' q.1 q.2) q.1 := by
    filter_upwards [hzP.eventually (Ioi_mem_nhds hPpos0)] with q hq
    exact (vx_hasDerivAt μ c φ hφ (Sx q.2) q.1 hq).neg
  -- data at the start and at the crossing
  have hPcross : (φ τ₀ x₀ : Phase) 0 ^ 2 + (φ τ₀ x₀ : Phase) 1 ^ 2 ≠ 0 := by
    have := hend; rw [(relPos_eq μ _).2] at this
    have h0 : (φ τ₀ x₀ : Phase) 0 ≠ 0 := by rintro h0; rw [h0] at this; simp at this
    positivity
  have hVxcross : 0 < Vx ((φ τ₀ x₀ : LeftEnergyState μ c) : Phase) := by
    have := hv τ₀ ⟨hτ₀, le_refl _⟩; rwa [(jv_eq μ _).1] at this
  have hf'pos : 0 < f' τ₀ r₀ := by
    simp only [hf', hΦ0]
    rw [XRd_eq _ hPcross]
    have : 0 < (φ τ₀ x₀ : Phase) 0 ^ 2 + (φ τ₀ x₀ : Phase) 1 ^ 2 := by positivity
    positivity
  have hh'neg : h' 0 r₀ < 0 := by
    simp only [hh', hΦ0, Flow.map_zero_apply]
    rw [Yd_eq μ _ hP0]
    have : 0 < (x₀ : Phase) 0 ^ 2 + (x₀ : Phase) 1 ^ 2 := by rw [hc1]; positivity
    nlinarith
  have hOmx := far_axis_omega_x_pos μ c hμ0 hμ1 hc _ x₀.2 hc0 (by rw [hc1]; exact hr₀.ne')
  have hk'neg : k' 0 r₀ < 0 := by
    simp only [hk', hΦ0, Flow.map_zero_apply]
    have : 0 < zNormSq (x₀ : Phase) := by unfold zNormSq; rw [hc1]; positivity
    have : 0 < Omx μ (x₀ : Phase) - 2 * Vy μ (x₀ : Phase) := by linarith
    have : 0 < 4 * zNormSq (x₀ : Phase) * (Omx μ (x₀ : Phase) - 2 * Vy μ (x₀ : Phase)) := by
      positivity
    linarith
  have hzero : ∀ r, (Sx r : Phase) 0 = 0 ∧ (Sx r : Phase) 3 = 0 ∧ (Sx r : Phase) 0 * (Sx r : Phase) 1 = 0 := by
    intro r
    rcases hSxall r with e | e
    · rw [e]; simp [farShootingStart]
    · rw [e, hc0, hc3]; simp
  have hh0 : ∀ r, h 0 r = 0 := by
    intro r
    simp only [hh, hΦdef, Flow.map_zero_apply, (relPos_eq μ _).2]
    rw [(hzero r).1]; ring
  have hk0 : ∀ r, k 0 r = 0 := by
    intro r
    simp only [hk, hΦdef, Flow.map_zero_apply, Vx]
    rw [(hzero r).1, (hzero r).2.1]; simp
  have hf0 : f τ₀ r₀ = 0 := by simp only [hf, hΦ0, hcross]
  have hmono := far_arc_mono μ c φ hφ x₀ τ₀ ⟨hτ₀, hlow, hend, hcross, hv⟩
  have hfneg : ∀ s ∈ Ico 0 τ₀, f s r₀ < 0 := by
    intro s hs
    simp only [hf, hΦ0]
    rw [← hcross]
    exact hmono ⟨hs.1, hs.2.le⟩ ⟨hτ₀.le, le_refl _⟩ hs.2
  have hhneg : ∀ s ∈ Ioc 0 τ₀, h s r₀ < 0 := by
    intro s hs
    simp only [hh, hΦ0]
    rcases eq_or_lt_of_le hs.2 with e | e
    · subst e; exact hend
    · exact hlow s ⟨hs.1, e⟩
  have hkneg : ∀ s ∈ Ioc 0 τ₀, k s r₀ < 0 := by
    intro s hs
    simp only [hk, hΦ0]
    have := hv s hs; rw [(jv_eq μ _).1] at this; linarith
  have hfc : ∀ s, ContinuousAt (uncurry f) (s, r₀) := fun s =>
    (cont_relPos0 μ).continuousAt.comp (hΦ s)
  have hhc : ∀ s, ContinuousAt (uncurry h) (s, r₀) := fun s =>
    (cont_relPos1 μ).continuousAt.comp (hΦ s)
  have hkc : ∀ s ∈ Ioc 0 τ₀, ContinuousAt (uncurry k) (s, r₀) := by
    intro s hs
    have hP : Φ s r₀ 0 ^ 2 + Φ s r₀ 1 ^ 2 ≠ 0 := by
      have := hhneg s hs
      simp only [hh, (relPos_eq μ _).2] at this
      have h0 : Φ s r₀ 0 ≠ 0 := by rintro h0; rw [h0] at this; simp at this
      positivity
    exact (ContinuousAt.comp (x := (s, r₀)) (cont_Vx _ hP) (hΦ s)).neg
  have hf'c : ContinuousAt (uncurry f') (τ₀, r₀) := cont_XRd.continuousAt.comp (hΦ τ₀)
  have hh'c : ContinuousAt (uncurry h') (0, r₀) := (cont_Yd μ).continuousAt.comp (hΦ 0)
  have hk'c : ContinuousAt (uncurry k') (0, r₀) := by
    have hP : Φ 0 r₀ 0 ^ 2 + Φ 0 r₀ 1 ^ 2 ≠ 0 := by
      rw [hΦ0]; simp only [Flow.map_zero_apply]; exact hP0
    have hD : 0 < secondCollisionDistanceSq (Φ 0 r₀) := by
      rw [hΦ0]; exact (mem_locus' _).2
    have c1 : ContinuousAt (fun q : ℝ × ℝ => Omx μ (uncurry Φ q)) (0, r₀) :=
      ContinuousAt.comp_of_eq (cont_Omx μ _ hP hD) (hΦ 0) rfl
    have c2 : ContinuousAt (fun q : ℝ × ℝ => Vy μ (uncurry Φ q)) (0, r₀) :=
      ContinuousAt.comp_of_eq (cont_Vy μ _ hP) (hΦ 0) rfl
    have c3 : ContinuousAt (fun q : ℝ × ℝ => zNormSq (uncurry Φ q)) (0, r₀) :=
      ContinuousAt.comp_of_eq cont_zNormSq.continuousAt (hΦ 0) rfl
    exact ((c3.const_mul 4).mul (c1.sub (c2.const_mul 2))).neg
  have hC : ContinuousAt (fun q : ℝ × ℝ => shootingCoordinates μ (Φ q.1 q.2)) (τ₀, r₀) := by
    have := cont_coords μ (Φ τ₀ r₀) (by rw [hΦ0]; exact hPcross) (by rw [hΦ0]; exact hVxcross.ne')
    exact ContinuousAt.comp (x := (τ₀, r₀)) this (hΦ τ₀)
  obtain ⟨a, ha, Ebox⟩ := box_of_eventually
    (fun s r => dist (shootingCoordinates μ (Φ s r)) (shootingCoordinates μ (Φ τ₀ r₀)) < ε)
    τ₀ r₀ (hC.eventually (Metric.ball_mem_nhds _ hε))
  have Ecross := transversal_crossing_persists r₀ τ₀ hτ₀ f h k f' h' k'
    hfc (fun s _ => hhc s) hkc
    (Eventually.of_forall fun q => hderf q.1 q.2) hf'c hf'pos
    (Eventually.of_forall fun q => hderh q.1 q.2) hh'c hh'neg
    hderk hk'c hk'neg
    hh0 hk0 hf0 hfneg hhneg hkneg a ha
  obtain ⟨δ, hδ, hfinal⟩ := Metric.eventually_nhds_iff.1 ((Ecross.and Ebox).and hSxev)
  refine ⟨δ, hδ, fun r hr => ?_⟩
  obtain ⟨⟨⟨τ, hτa, hτ, hfτ, -, hhk⟩, hbox⟩, hSr⟩ := hfinal (by rwa [Real.dist_eq])
  refine ⟨Sx r, hSr, τ, ⟨hτ, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro u hu
    exact (hhk u ⟨hu.1, hu.2.le⟩).1
  · exact (hhk τ ⟨hτ, le_refl _⟩).1
  · exact hfτ
  · intro u hu
    have := (hhk u hu).2
    simp only [hk, hΦdef] at this
    rw [(jv_eq μ _).1]; linarith
  · have := hbox τ ⟨by linarith [(abs_lt.1 hτa).1], by linarith [(abs_lt.1 hτa).2]⟩
    simpa [hΦdef, hSx0] using this
