-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_far_arc_limit_rest
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T19:01:59.418986+00:00
-- url     : https://prove2.me/submissions/c2474255-0404-49ea-8a33-0cda6ce1355e

import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_collision_strict
import Definitions.Def_BirkhoffGlobalSection
import Definitions.Def_BirkhoffShootingCoordinates
import Theorems.Thm_BirkhoffGlobalSection_partial_derivative_eq_update_deriv
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_circle_hamiltonian_lower_bound
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_realizes_first_critical_value
import Theorems.Thm_BirkhoffGlobalSection_leftCollisionPoint_mem_leftEnergyComponent
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
noncomputable def farR (μ c r : ℝ) : ℝ :=
  (1 - μ) + r ^ 2 * ((2 * r ^ 2 + μ) ^ 2 + 2 * μ / (1 + 2 * r ^ 2) - 2 * c)

lemma farStart_eq (μ c r : ℝ) :
    farShootingStart μ c r = ![0, r, r * (2 * r ^ 2 + μ) - Real.sqrt (farR μ c r), 0] := rfl

lemma farStart_Vy (μ c r : ℝ) (hr : r ≠ 0) :
    Vy μ (farShootingStart μ c r) = -(Real.sqrt (farR μ c r) / r) := by
  simp only [Vy, farStart_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  field_simp; ring

lemma farR_continuous (μ c : ℝ) : Continuous (farR μ c) := by
  unfold farR
  have : ∀ r : ℝ, 1 + 2 * r ^ 2 ≠ 0 := fun r => by positivity
  fun_prop (disch := exact this _)

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

-- ===== Solutions.Abstract =====
section Abstract

variable {X : Type*} [TopologicalSpace X]

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

/-- The time-`(±s)` state along the flow from a family of starts. -/
lemma flow_state_continuousAt {μ c : ℝ} (φ : Flow ℝ (LeftEnergyState μ c))
    (Sx : ℝ → LeftEnergyState μ c) (r₀ : ℝ) (hS : ContinuousAt Sx r₀) (σ : ℝ) (s : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => ((φ (σ * q.1) (Sx q.2) : LeftEnergyState μ c) : Phase))
      (s, r₀) := by
  have hpair : ContinuousAt (fun q : ℝ × ℝ => (σ * q.1, Sx q.2)) (s, r₀) :=
    ContinuousAt.prodMk (by fun_prop) (hS.comp continuousAt_snd)
  exact continuous_subtype_val.continuousAt.comp (φ.cont'.continuousAt.comp hpair)

-- ===== Solutions.CM19 =====
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

-- ===== Solutions.CM14 =====
/-- Energy at a collision state fixes the speed. -/
lemma collision_speed (μ c : ℝ) (s : Phase) (hs : s ∈ leftEnergyComponent μ c)
    (h0 : s 0 = 0) (h1 : s 1 = 0) : s 2 ^ 2 + s 3 ^ 2 = 1 - μ := by
  have hK := (connectedComponentIn_subset _ _ hs).1
  simp only [leviCivitaHamiltonian, wNormSq, zNormSq, h0, h1] at hK
  simp at hK
  linarith

-- ===== Solutions.CM21 =====
lemma omega_y_nonneg (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
    (s : Phase) (hs : s ∈ leftEnergyComponent μ c) (hy : 4 * s 0 * s 1 ≤ 0) : 0 ≤ Omy μ s := by
  rcases lt_or_eq_of_le hy with h | h
  · exact (omega_y_pos μ c hμ0 hμ1 hc s hs h).le
  · unfold Omy; rw [h]; simp

/-- Compact tube: a positive function along the orbit of `Sx b` on a compact time interval
stays positive along the orbits of `Sx r` for `r` near `b`. -/
lemma tube_pos {μ c : ℝ} (φ : Flow ℝ (LeftEnergyState μ c)) (Sx : ℝ → LeftEnergyState μ c)
    (b : ℝ) (hS : ContinuousAt Sx b) (f : Phase → ℝ) (hf : Continuous f) (a e : ℝ)
    (hpos : ∀ t ∈ Icc a e, 0 < f ((φ t (Sx b) : LeftEnergyState μ c) : Phase)) :
    ∀ᶠ r in 𝓝 b, ∀ t ∈ Icc a e, 0 < f ((φ t (Sx r) : LeftEnergyState μ c) : Phase) := by
  apply (isCompact_Icc).eventually_forall_of_forall_eventually
  intro t ht
  have hc := flow_state_continuousAt φ Sx b hS 1 t
  have hsw : ContinuousAt (Prod.swap : ℝ × ℝ → ℝ × ℝ) (b, t) := continuous_swap.continuousAt
  have hc2 : ContinuousAt (fun q : ℝ × ℝ => ((φ (1 * q.1) (Sx q.2) : LeftEnergyState μ c) : Phase))
      (Prod.swap (b, t)) := hc
  have hc' : ContinuousAt (fun q : ℝ × ℝ => f ((φ q.2 (Sx q.1) : LeftEnergyState μ c) : Phase))
      (b, t) := by
    have := (hf.continuousAt).comp (hc2.comp hsw)
    have e : (fun q : ℝ × ℝ => f ((φ q.2 (Sx q.1) : LeftEnergyState μ c) : Phase)) =
        f ∘ (fun q : ℝ × ℝ => ((φ (1 * q.1) (Sx q.2) : LeftEnergyState μ c) : Phase)) ∘ Prod.swap := by
      funext q; simp
    rw [e]; exact this
  exact hc'.eventually (Ioi_mem_nhds (hpos t ht))

/-- One-sided limits of a sign condition along the family. -/
lemma limit_nonpos {μ c : ℝ} (φ : Flow ℝ (LeftEnergyState μ c)) (Sx : ℝ → LeftEnergyState μ c)
    (b : ℝ) (hS : ContinuousAt Sx b) (f : Phase → ℝ) (hf : Continuous f) (t : ℝ)
    (hneg : ∀ᶠ r in 𝓝[<] b, f ((φ t (Sx r) : LeftEnergyState μ c) : Phase) ≤ 0) :
    f ((φ t (Sx b) : LeftEnergyState μ c) : Phase) ≤ 0 := by
  have hc := flow_state_continuousAt φ Sx b hS 1 t
  have hc' : ContinuousAt (fun r : ℝ => f ((φ t (Sx r) : LeftEnergyState μ c) : Phase)) b := by
    have h2 : ContinuousAt (fun r : ℝ => (t, r)) b := by fun_prop
    have := (hf.continuousAt).comp (hc.comp h2)
    simpa [Function.comp_def] using this
  exact le_of_tendsto (hc'.tendsto.mono_left nhdsWithin_le_nhds) hneg

-- ===== Solutions.CM25 =====
lemma comp_D_pos {μ c : ℝ} (s : Phase) (hs : s ∈ leftEnergyComponent μ c) :
    0 < secondCollisionDistanceSq s := (connectedComponentIn_subset _ _ hs).2

/-- The far start at the first bad parameter lies on the component. -/
lemma far_start_limit_mem (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (b : ℝ) (hb : 0 < b)
    (hgood : ∀ r ∈ Ioo 0 b, farShootingStart μ c r ∈ leftEnergyComponent μ c) :
    farShootingStart μ c b ∈ leftEnergyComponent μ c := by
  have hK := left_energy_component_compact μ c hμ0 hμ1 hc
  have hev : ∀ᶠ r in 𝓝[<] b, farShootingStart μ c r ∈ leftEnergyComponent μ c := by
    filter_upwards [Ioo_mem_nhdsLT (half_lt_self hb)] with r hr
    exact hgood r ⟨lt_trans (half_pos hb) hr.1, hr.2⟩
  exact hK.isClosed.mem_of_tendsto
    (((farStart_continuous μ c).continuousAt).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio b))) hev

/-- A family of states through the far starts below `b`, continuous at `b`. -/
lemma far_family (μ c : ℝ) (b : ℝ) (hb : 0 < b)
    (xb : LeftEnergyState μ c) (hxb : (xb : Phase) = farShootingStart μ c b)
    (hgood : ∀ r ∈ Ioo 0 b, farShootingStart μ c r ∈ leftEnergyComponent μ c) :
    ∃ Sx : ℝ → LeftEnergyState μ c, Sx b = xb ∧ ContinuousAt Sx b ∧
      ∀ r ∈ Icc (b / 2) b, (Sx r : Phase) = farShootingStart μ c r := by
  set St : ℝ → Phase := fun r => farShootingStart μ c (max (b / 2) (min r b)) with hSt
  have hStb : St b = farShootingStart μ c b := by
    simp only [hSt, min_self, max_eq_right (half_lt_self hb).le]
  have hStc : ContinuousAt St b :=
    ((farStart_continuous μ c).comp (by fun_prop)).continuousAt
  have hmem : ∀ r, St r ∈ leftEnergyComponent μ c := by
    intro r
    simp only [hSt]
    rcases lt_or_ge r b with h | h
    · rcases lt_or_ge (b / 2) r with h' | h'
      · rw [min_eq_left h.le, max_eq_right h'.le]; exact hgood r ⟨by linarith, h⟩
      · rw [min_eq_left h.le, max_eq_left h']; exact hgood (b / 2) ⟨half_pos hb, half_lt_self hb⟩
    · rw [min_eq_right h, max_eq_right (half_lt_self hb).le, ← hxb]; exact xb.2
  refine ⟨fun r => ⟨St r, hmem r⟩, Subtype.ext (by simp only; rw [hStb, hxb]), ?_, ?_⟩
  · rw [Topology.IsInducing.subtypeVal.continuousAt_iff]; exact hStc
  · intro r hr; simp only [hSt]; rw [min_eq_left hr.2, max_eq_right hr.1]

/-- A moving far-axis start enters `{x₁ < 0, x₂ < 0, v₁ > 0}` in forward time. -/
lemma far_start_open (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c)
    (hx0 : (x : Phase) 0 = 0) (hx1 : 0 < (x : Phase) 1) (hx3 : (x : Phase) 3 = 0)
    (hv : Vy μ (x : Phase) < 0) :
    ∃ ε > 0, ∀ t ∈ Ioo 0 ε,
      relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0 < 0 ∧
      relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0 ∧
      0 < Vx ((φ t x : LeftEnergyState μ c) : Phase) := by
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → Phase, γ = fun u => ((φ u x : LeftEnergyState μ c) : Phase) :=
    ⟨_, rfl⟩
  have hγd : ∀ u, γ u = ((φ u x : LeftEnergyState μ c) : Phase) := fun u => by rw [hγ]
  have hγ0 : γ 0 = (x : Phase) := by rw [hγd]; simp
  have hγc : Continuous γ := by
    rw [hγ]; exact continuous_subtype_val.comp (φ.continuous continuous_id continuous_const)
  set X : ℝ → ℝ := fun t => relativePosition μ (γ t) 0 with hX
  set Y : ℝ → ℝ := fun t => relativePosition μ (γ t) 1 with hY
  have hXc : Continuous X := (cont_relPos0 μ).comp hγc
  have hYd : ∀ t, HasDerivAt Y (Yd μ (γ t)) t := by
    intro t
    have hfun : Y = fun v => relativePosition μ ((φ v x : LeftEnergyState μ c) : Phase) 1 := by
      funext v; simp only [hY, hγd]
    rw [hfun, hγd]; exact y_hasDerivAt μ c φ hφ x t
  have hP0 : (x : Phase) 0 ^ 2 + (x : Phase) 1 ^ 2 ≠ 0 := by positivity
  have hD0 := comp_D_pos (x : Phase) x.2
  have hVyc : ContinuousAt (fun t => Vy μ (γ t)) 0 := by
    have := cont_Vy μ (x : Phase) hP0; rw [← hγ0] at this; exact this.comp hγc.continuousAt
  have hFc : ContinuousAt (fun t => Omx μ (γ t) - 2 * Vy μ (γ t)) 0 := by
    have h1 := cont_Omx μ (x : Phase) hP0 hD0; rw [← hγ0] at h1
    exact (h1.comp hγc.continuousAt).sub (hVyc.const_mul 2)
  have hPc : ContinuousAt (fun t => zNormSq (γ t)) 0 := (cont_zNormSq.comp hγc).continuousAt
  have hX0 : X 0 < 0 := by
    simp only [hX]; rw [hγ0, (relPos_eq μ _).1, hx0]; nlinarith
  have hF0 : 0 < Omx μ (γ 0) - 2 * Vy μ (γ 0) := by
    rw [hγ0]
    have := far_axis_omega_x_pos μ c hμ0 hμ1 hc _ x.2 hx0 hx1.ne'
    linarith
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), Vy μ (γ t) < 0 ∧ 0 < zNormSq (γ t) ∧ X t < 0 ∧
      0 < Omx μ (γ t) - 2 * Vy μ (γ t) := by
    refine (hVyc.eventually (Iio_mem_nhds (by show Vy μ (γ 0) < 0; rw [hγ0]; exact hv))).and
      ((hPc.eventually (Ioi_mem_nhds ?_)).and ((hXc.continuousAt.eventually (Iio_mem_nhds hX0)).and
        (hFc.eventually (Ioi_mem_nhds hF0))))
    show 0 < zNormSq (γ 0); rw [hγ0]; unfold zNormSq; positivity
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hin : ∀ t, 0 ≤ t → t ≤ ε / 2 → Vy μ (γ t) < 0 ∧ 0 < zNormSq (γ t) ∧ X t < 0 ∧
      0 < Omx μ (γ t) - 2 * Vy μ (γ t) := by
    intro t h1 h2; apply hball; rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith
  have hYanti : StrictAntiOn Y (Icc 0 (ε / 2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t _ => (hYd t).continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    rw [(hYd t).deriv]
    obtain ⟨h1, h2, -⟩ := hin t ht.1.le ht.2.le
    have hP2 := h2; unfold zNormSq at hP2
    rw [Yd_eq μ _ hP2.ne']
    have : 0 < 4 * (γ t 0 ^ 2 + γ t 1 ^ 2) := by positivity
    nlinarith
  have hVxd : ∀ t, 0 ≤ t → t ≤ ε / 2 → HasDerivAt (fun v => Vx (γ v))
      (4 * zNormSq (γ t) * (Omx μ (γ t) - 2 * Vy μ (γ t))) t := by
    intro t h1 h2
    have := vx_hasDerivAt μ c φ hφ x t (by rw [← hγd]; exact (hin t h1 h2).2.1)
    have hfun : (fun v => Vx (γ v)) = fun v => Vx ((φ v x : LeftEnergyState μ c) : Phase) := by
      funext v; rw [hγd]
    rw [hfun, hγd]; exact this
  have hVxmono : StrictMonoOn (fun v => Vx (γ v)) (Icc 0 (ε / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t ht => (hVxd t ht.1 ht.2).continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    rw [(hVxd t ht.1.le ht.2.le).deriv]
    obtain ⟨-, h2, -, h4⟩ := hin t ht.1.le ht.2.le
    positivity
  have hY0 : Y 0 = 0 := by simp only [hY]; rw [hγ0, (relPos_eq μ _).2, hx0]; ring
  have hVx0 : Vx (γ 0) = 0 := by rw [hγ0]; unfold Vx; rw [hx0, hx3]; ring
  refine ⟨ε / 2, half_pos hε, fun t ht => ?_⟩
  have h1 := (hin t ht.1.le ht.2.le).2.2.1
  have h2 := hYanti ⟨le_refl _, (half_pos hε).le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
  have h3 := hVxmono ⟨le_refl _, (half_pos hε).le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
  rw [hY0] at h2
  simp only at h3; rw [hVx0] at h3
  simp only [hX, hY, hγd] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

-- ===== Solutions.CM26 =====
set_option maxHeartbeats 4000000 in
/-- The far family cannot run up to the zero-velocity curve: at the first bad parameter the
far start is still moving. -/
theorem far_start_moving (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (b : ℝ) (hb : 0 < b)
    (hgood : ∀ r ∈ Ioo 0 b, ∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c r ∧
      ∃ τ : ℝ, IsFarShootingArc φ x τ)
    (xb : LeftEnergyState μ c) (hxb : (xb : Phase) = farShootingStart μ c b) :
    Vy μ (xb : Phase) < 0 := by
  have hgood' : ∀ r ∈ Ioo 0 b, farShootingStart μ c r ∈ leftEnergyComponent μ c := by
    intro r hr; obtain ⟨x, hx, -⟩ := hgood r hr; rw [← hx]; exact x.2
  obtain ⟨Sx, hSxb, hSxc, hSx⟩ := far_family μ c b hb xb hxb hgood'
  have hb0 : (xb : Phase) 0 = 0 := by rw [hxb]; simp [farShootingStart]
  have hb1 : (xb : Phase) 1 = b := by rw [hxb]; simp [farShootingStart]
  have hb3 : (xb : Phase) 3 = 0 := by rw [hxb]; simp [farShootingStart]
  have hVnp : Vy μ (xb : Phase) ≤ 0 := by
    rw [hxb, farStart_Vy μ c b hb.ne']; have : 0 ≤ Real.sqrt (farR μ c b) / b := by positivity
    linarith
  rcases eq_or_lt_of_le hVnp with hV0 | hV0
  swap; · exact hV0
  exfalso
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → Phase, γ = fun u => ((φ u xb : LeftEnergyState μ c) : Phase) :=
    ⟨_, rfl⟩
  have hγd : ∀ u, γ u = ((φ u xb : LeftEnergyState μ c) : Phase) := fun u => by rw [hγ]
  have hγ0 : γ 0 = (xb : Phase) := by rw [hγd]; simp
  have hγc : Continuous γ := by
    rw [hγ]; exact continuous_subtype_val.comp (φ.continuous continuous_id continuous_const)
  have hmem : ∀ u, γ u ∈ leftEnergyComponent μ c := fun u => by rw [hγd]; exact (φ u xb).2
  set X : ℝ → ℝ := fun t => relativePosition μ (γ t) 0 with hX
  set Y : ℝ → ℝ := fun t => relativePosition μ (γ t) 1 with hY
  have hXc : Continuous X := (cont_relPos0 μ).comp hγc
  have hX0 : X 0 < 0 := by
    simp only [hX]; rw [hγ0, (relPos_eq μ _).1, hb1, hb0]; nlinarith
  -- near the start: `x₁ < 0`, and the force pushes `v₁` up
  have hP0 : (xb : Phase) 0 ^ 2 + (xb : Phase) 1 ^ 2 ≠ 0 := by rw [hb0, hb1]; positivity
  have hVyc : ContinuousAt (fun t => Vy μ (γ t)) 0 := by
    have := cont_Vy μ (xb : Phase) hP0; rw [← hγ0] at this; exact this.comp hγc.continuousAt
  have hFc : ContinuousAt (fun t => Omx μ (γ t) - 2 * Vy μ (γ t)) 0 := by
    have h1 := cont_Omx μ (xb : Phase) hP0 (comp_D_pos _ xb.2); rw [← hγ0] at h1
    exact (h1.comp hγc.continuousAt).sub (hVyc.const_mul 2)
  have hF0 : 0 < Omx μ (γ 0) - 2 * Vy μ (γ 0) := by
    rw [hγ0, hV0]
    have := far_axis_omega_x_pos μ c hμ0 hμ1 hc _ xb.2 hb0 (by rw [hb1]; exact hb.ne')
    linarith
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    ((hXc.continuousAt.eventually (Iio_mem_nhds hX0)).and (hFc.eventually (Ioi_mem_nhds hF0)))
  set t1 := ε / 2 with ht1
  have ht10 : 0 < t1 := half_pos hε
  have hin : ∀ t ∈ Icc 0 t1, X t < 0 ∧ 0 < Omx μ (γ t) - 2 * Vy μ (γ t) := by
    intro t ht; apply hball; rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hPpos : ∀ t ∈ Icc 0 t1, 0 < zNormSq (γ t) := by
    intro t ht
    have := (hin t ht).1; simp only [hX] at this; rw [(relPos_eq μ _).1] at this
    unfold zNormSq; nlinarith [sq_nonneg (γ t 0)]
  -- nearby far arcs are longer than `t1`: limits `x₂ ≤ 0`
  have htube := tube_pos φ Sx b hSxc (fun s => -relativePosition μ s 0) (cont_relPos0 μ).neg 0 t1
    (by intro t ht; rw [hSxb, ← hγd]; have := (hin t ht).1; simp only [hX] at this; linarith)
  have hYle : ∀ t ∈ Ioo 0 t1, Y t ≤ 0 := by
    intro t ht
    have := limit_nonpos φ Sx b hSxc (fun s => relativePosition μ s 1) (cont_relPos1 μ) t (by
      have hev : ∀ᶠ r in 𝓝[<] b, r ∈ Ioo (b / 2) b := Ioo_mem_nhdsLT (half_lt_self hb)
      filter_upwards [hev, nhdsWithin_le_nhds htube] with r hr htr
      obtain ⟨x, hx, τ, harc⟩ := hgood r ⟨lt_trans (half_pos hb) hr.1, hr.2⟩
      have hxS : x = Sx r := Subtype.ext (by rw [hx, hSx r ⟨hr.1.le, hr.2.le⟩])
      rw [hxS] at harc
      obtain ⟨hτ, hlow, -, hcross, -⟩ := harc
      have hτt : t1 < τ := by
        by_contra hle; push Not at hle
        have := htr τ ⟨hτ.le, hle⟩
        rw [hcross] at this; simp at this
      exact (hlow t ⟨ht.1, by linarith [ht.2]⟩).le)
    rw [hSxb, ← hγd] at this; exact this
  -- the rest orbit rises above the axis
  have hVxd : ∀ t ∈ Icc 0 t1, HasDerivAt (fun v => Vx (γ v))
      (4 * zNormSq (γ t) * (Omx μ (γ t) - 2 * Vy μ (γ t))) t := by
    intro t ht
    have := vx_hasDerivAt μ c φ hφ xb t (by rw [← hγd]; exact hPpos t ht)
    have hfun : (fun v => Vx (γ v)) = fun v => Vx ((φ v xb : LeftEnergyState μ c) : Phase) := by
      funext v; rw [hγd]
    rw [hfun, hγd]; exact this
  have hVxmono : StrictMonoOn (fun v => Vx (γ v)) (Icc 0 t1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t ht => (hVxd t ht).continuousAt.continuousWithinAt)
    intro t ht
    have ht' := interior_subset ht
    rw [(hVxd t ht').deriv]
    have := (hin t ht').2; have := hPpos t ht'
    positivity
  have hVx0 : Vx (γ 0) = 0 := by rw [hγ0]; unfold Vx; rw [hb0, hb3]; ring
  have hVyd : ∀ t ∈ Icc 0 t1, HasDerivAt (fun v => Vy μ (γ v))
      (4 * zNormSq (γ t) * (2 * Vx (γ t) + Omy μ (γ t))) t := by
    intro t ht
    have := vy_hasDerivAt μ c φ hφ xb t (by rw [← hγd]; exact hPpos t ht)
    have hfun : (fun v => Vy μ (γ v)) = fun v => Vy μ ((φ v xb : LeftEnergyState μ c) : Phase) := by
      funext v; rw [hγd]
    rw [hfun, hγd]; exact this
  have hVymono : StrictMonoOn (fun v => Vy μ (γ v)) (Icc 0 t1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t ht => (hVyd t ht).continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    rw [(hVyd t ⟨ht.1.le, ht.2.le⟩).deriv]
    have hy : 4 * γ t 0 * γ t 1 ≤ 0 := by
      have := hYle t ht; simp only [hY] at this; rwa [(relPos_eq μ _).2] at this
    have h1 := omega_y_nonneg μ c hμ0 hμ1 hc (γ t) (hmem t) hy
    have h2 := hVxmono ⟨le_refl _, ht10.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
    simp only at h2; rw [hVx0] at h2
    have := hPpos t ⟨ht.1.le, ht.2.le⟩
    positivity
  have hYd : ∀ t, HasDerivAt Y (Yd μ (γ t)) t := by
    intro t
    have hfun : Y = fun v => relativePosition μ ((φ v xb : LeftEnergyState μ c) : Phase) 1 := by
      funext v; simp only [hY, hγd]
    rw [hfun, hγd]; exact y_hasDerivAt μ c φ hφ xb t
  have hYmono : StrictMonoOn Y (Icc 0 t1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t _ => (hYd t).continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    rw [(hYd t).deriv]
    have hP := hPpos t ⟨ht.1.le, ht.2.le⟩
    have hP' := hP; unfold zNormSq at hP'
    rw [Yd_eq μ _ hP'.ne']
    have := hVymono ⟨le_refl _, ht10.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
    simp only at this
    rw [hγ0, hV0] at this
    unfold zNormSq at hP
    positivity
  have := hYmono ⟨le_refl _, ht10.le⟩ ⟨by linarith, by linarith⟩ (by linarith : (0:ℝ) < t1 / 2)
  have hY0 : Y 0 = 0 := by simp only [hY]; rw [hγ0, (relPos_eq μ _).2, hb0]; ring
  have := hYle (t1 / 2) ⟨by linarith, by linarith⟩
  linarith

-- ===== Solutions.CM29 =====
/-! Birkhoff's identity (59): the angular momentum about the primary along far arcs. -/

/-- The angular momentum `L = x₁ v₂ - x₂ v₁` about the primary, as a polynomial in the
Levi-Civita state (valid off collision, see `Lpoly_eq`). -/
noncomputable def Lpoly (μ : ℝ) (s : Phase) : ℝ :=
  2 * (s 0 * s 3 - s 1 * s 2) - μ * (2 * (s 0 ^ 2 - s 1 ^ 2)) +
    (2 * (s 0 ^ 2 - s 1 ^ 2)) ^ 2 + (4 * s 0 * s 1) ^ 2

lemma cont_Lpoly (μ : ℝ) : Continuous (Lpoly μ) := by unfold Lpoly; fun_prop

lemma Lpoly_eq (μ : ℝ) (s : Phase) (hP : s 0 ^ 2 + s 1 ^ 2 ≠ 0) :
    Lpoly μ s = relativePosition μ s 0 * Vy μ s - relativePosition μ s 1 * Vx s := by
  rw [(relPos_eq μ s).1, (relPos_eq μ s).2]; unfold Lpoly Vy Vx; field_simp; ring

/-- The torque identity behind Birkhoff's (59). -/
lemma torque_eq (μ : ℝ) (s : Phase) :
    relativePosition μ s 0 * Omy μ s - relativePosition μ s 1 * Omx μ s =
      μ * relativePosition μ s 1 *
        (1 - 1 / Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ - 1 + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) ^ 3) := by
  rw [(relPos_eq μ s).1, (relPos_eq μ s).2]; unfold Omx Omy; ring

/-- On the far side below the axis the torque of the second primary is negative. -/
lemma torque_neg (μ : ℝ) (hμ0 : 0 < μ) (s : Phase) (hX : relativePosition μ s 0 ≤ 0)
    (hY : relativePosition μ s 1 < 0) :
    relativePosition μ s 0 * Omy μ s - relativePosition μ s 1 * Omx μ s < 0 := by
  rw [torque_eq]
  set R := Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ - 1 + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) with hR
  rw [(relPos_eq μ s).1] at hX; rw [(relPos_eq μ s).2] at hY ⊢
  have hR1 : 1 < R := by
    rw [hR, Real.lt_sqrt (by norm_num)]
    have : 0 < (4 * s 0 * s 1) ^ 2 := by nlinarith
    nlinarith
  have h3 : 1 < R ^ 3 := one_lt_pow₀ hR1 (by norm_num)
  have : 0 < 1 - 1 / R ^ 3 := by
    rw [sub_pos, div_lt_one (by positivity)]; exact h3
  have := mul_pos hμ0 this
  nlinarith

/-- The derivative of the angular momentum along the flow. -/
lemma L_hasDerivAt (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ)
    (hP : 0 < zNormSq ((φ t x : LeftEnergyState μ c) : Phase)) :
    HasDerivAt (fun u => Lpoly μ ((φ u x : LeftEnergyState μ c) : Phase))
      (4 * zNormSq ((φ t x : LeftEnergyState μ c) : Phase) *
        (2 * (relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0 *
            Vx ((φ t x : LeftEnergyState μ c) : Phase) +
          relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 *
            Vy μ ((φ t x : LeftEnergyState μ c) : Phase)) +
        (relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0 *
            Omy μ ((φ t x : LeftEnergyState μ c) : Phase) -
          relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 *
            Omx μ ((φ t x : LeftEnergyState μ c) : Phase)))) t := by
  set γ : ℝ → Phase := fun u => ((φ u x : LeftEnergyState μ c) : Phase) with hγ
  have hγc : Continuous γ :=
    continuous_subtype_val.comp (φ.continuous continuous_id continuous_const)
  have hPev : ∀ᶠ u in 𝓝 t, 0 < zNormSq (γ u) :=
    (cont_zNormSq.comp hγc).continuousAt.eventually (Ioi_mem_nhds hP)
  have hX := xrel_hasDerivAt' μ c φ hφ x t
  have hY := y_hasDerivAt μ c φ hφ x t
  have hVx := vx_hasDerivAt μ c φ hφ x t hP
  have hVy := vy_hasDerivAt μ c φ hφ x t hP
  have hprod := (hX.mul hVy).sub (hY.mul hVx)
  have hP' := hP; unfold zNormSq at hP'
  have heq : (fun u => Lpoly μ (γ u)) =ᶠ[𝓝 t] fun u =>
      relativePosition μ (γ u) 0 * Vy μ (γ u) - relativePosition μ (γ u) 1 * Vx (γ u) := by
    filter_upwards [hPev] with u hu
    unfold zNormSq at hu; exact Lpoly_eq μ _ hu.ne'
  refine (hprod.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [XRd_eq _ hP'.ne', Yd_eq μ _ hP'.ne']; unfold zNormSq; ring

/-- Where the angular momentum vanishes on the far side below the axis with `v₁ ≥ 0`, it is
strictly decreasing (Birkhoff's identity (59)). -/
lemma L_deriv_neg (μ : ℝ) (hμ0 : 0 < μ) (s : Phase) (hP : 0 < s 0 ^ 2 + s 1 ^ 2)
    (hX : relativePosition μ s 0 < 0) (hY : relativePosition μ s 1 < 0) (hVx : 0 ≤ Vx s)
    (hL : Lpoly μ s = 0) :
    2 * (relativePosition μ s 0 * Vx s + relativePosition μ s 1 * Vy μ s) +
      (relativePosition μ s 0 * Omy μ s - relativePosition μ s 1 * Omx μ s) < 0 := by
  have ht := torque_neg μ hμ0 s hX.le hY
  rw [Lpoly_eq μ s hP.ne'] at hL
  set X := relativePosition μ s 0
  set Y := relativePosition μ s 1
  have hVy : Vy μ s = Y * Vx s / X := by rw [eq_div_iff hX.ne]; linarith
  have : X * Vx s + Y * Vy μ s ≤ 0 := by
    rw [hVy]
    have e : X * Vx s + Y * (Y * Vx s / X) = Vx s * (X ^ 2 + Y ^ 2) / X := by field_simp
    rw [e]
    exact div_nonpos_of_nonneg_of_nonpos (by positivity) hX.le
  linarith

/-- A function with negative derivative is larger just to the left. -/
lemma left_gt_of_deriv_neg {f : ℝ → ℝ} {a d : ℝ} (hf : HasDerivAt f d a) (hd : d < 0) :
    ∀ᶠ u in 𝓝[<] a, f a < f u := by
  have h := (hasDerivAt_iff_tendsto_slope.1 hf).mono_left
    (nhdsWithin_mono a (fun u (hu : u < a) => ne_of_lt hu))
  filter_upwards [h.eventually (Iio_mem_nhds hd), self_mem_nhdsWithin] with u hu hlt
  rw [slope_def_field] at hu
  have hlt' : u < a := hlt
  have hua : u - a < 0 := by linarith
  by_contra hle; push Not at hle
  have : 0 ≤ (f u - f a) / (u - a) := div_nonneg_of_nonpos (by linarith) hua.le
  linarith

set_option maxHeartbeats 4000000 in
/-- Along a far shooting arc the angular momentum about the primary is nonnegative. -/
theorem far_arc_L_nonneg (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (x : LeftEnergyState μ c) (τ : ℝ) (harc : IsFarShootingArc φ x τ) :
    ∀ t ∈ Ioc 0 τ, 0 ≤ Lpoly μ ((φ t x : LeftEnergyState μ c) : Phase) := by
  obtain ⟨hτ, hlow, hend, hcross, hvx⟩ := harc
  set γ : ℝ → Phase := fun u => ((φ u x : LeftEnergyState μ c) : Phase) with hγ
  have hγc : Continuous γ :=
    continuous_subtype_val.comp (φ.continuous continuous_id continuous_const)
  have hYneg : ∀ t ∈ Ioc 0 τ, relativePosition μ (γ t) 1 < 0 := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]; exact hend
    · exact hlow t ⟨ht.1, h⟩
  have hPpos : ∀ t ∈ Ioc 0 τ, 0 < zNormSq (γ t) := by
    intro t ht
    have hy := hYneg t ht; rw [(relPos_eq μ _).2] at hy
    have : γ t 0 ≠ 0 := by rintro h0; rw [h0] at hy; simp at hy
    unfold zNormSq; positivity
  have hVx : ∀ t ∈ Ioc 0 τ, 0 < Vx (γ t) := by
    intro t ht; have := hvx t ht; rwa [(jv_eq μ _).1] at this
  -- `x₁ < 0` before the crossing
  have hXd : ∀ t, HasDerivAt (fun u => relativePosition μ (γ u) 0) (XRd (γ t)) t :=
    fun t => xrel_hasDerivAt' μ c φ hφ x t
  have hXneg : ∀ t ∈ Ioo 0 τ, relativePosition μ (γ t) 0 < 0 := by
    intro t ht
    have hmono : StrictMonoOn (fun u => relativePosition μ (γ u) 0) (Icc t τ) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
        (fun u _ => (hXd u).continuousAt.continuousWithinAt)
      intro u hu; rw [interior_Icc] at hu
      have hu' : u ∈ Ioc 0 τ := ⟨by linarith [ht.1, hu.1], hu.2.le⟩
      have hP := hPpos u hu'; have hP' := hP; unfold zNormSq at hP'
      rw [(hXd u).deriv, XRd_eq _ hP'.ne']
      have := hVx u hu'; unfold zNormSq at hP; positivity
    have := hmono ⟨le_refl _, ht.2.le⟩ ⟨ht.2.le, le_refl _⟩ ht.2
    simp only at this; rw [hcross] at this; exact this
  have hLc : Continuous fun u => Lpoly μ (γ u) := (cont_Lpoly μ).comp hγc
  have hLτ : 0 < Lpoly μ (γ τ) := by
    have hP := hPpos τ ⟨hτ, le_refl _⟩; unfold zNormSq at hP
    rw [Lpoly_eq μ _ hP.ne', hcross]
    have := hVx τ ⟨hτ, le_refl _⟩
    have := hend
    nlinarith
  intro t ht
  by_contra hneg; push Not at hneg
  rcases eq_or_lt_of_le ht.2 with htτ | htτ
  · rw [htτ] at hneg; linarith
  -- the first zero of `L` after `t`
  set K := Icc t τ ∩ {u | 0 ≤ Lpoly μ (γ u)} with hK
  have hKc : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const hLc)
  have hKne : K.Nonempty := ⟨τ, ⟨htτ.le, le_refl _⟩, hLτ.le⟩
  obtain ⟨N, ⟨hNI, hNL⟩, hNmin⟩ := hKc.exists_isLeast hKne
  have hNt : t < N := by
    rcases eq_or_lt_of_le hNI.1 with h | h
    · rw [← h] at hNL; simp only [mem_setOf_eq] at hNL; linarith
    · exact h
  have hbefore : ∀ u ∈ Ico t N, Lpoly μ (γ u) < 0 := by
    intro u hu
    by_contra h; push Not at h
    have := hNmin ⟨⟨hu.1, le_trans hu.2.le hNI.2⟩, h⟩
    linarith [hu.2]
  have hN0 : Lpoly μ (γ N) = 0 := by
    apply le_antisymm _ hNL
    exact le_of_tendsto (hLc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio N)))
      (by filter_upwards [Ioo_mem_nhdsLT hNt] with u hu; exact (hbefore u ⟨hu.1.le, hu.2⟩).le)
  have hNτ : N < τ := by
    rcases eq_or_lt_of_le hNI.2 with h | h
    · rw [h] at hN0; linarith
    · exact h
  have hNI' : N ∈ Ioo 0 τ := ⟨by linarith [ht.1], hNτ⟩
  have hNc : N ∈ Ioc 0 τ := ⟨hNI'.1, hNτ.le⟩
  have hP := hPpos N hNc; have hP' := hP; unfold zNormSq at hP'
  have hd := L_hasDerivAt μ c φ hφ x N hP
  have hneg' := L_deriv_neg μ hμ0 (γ N) hP' (hXneg N hNI') (hYneg N hNc) (hVx N hNc).le hN0
  have hdneg : 4 * zNormSq (γ N) *
      (2 * (relativePosition μ (γ N) 0 * Vx (γ N) + relativePosition μ (γ N) 1 * Vy μ (γ N)) +
        (relativePosition μ (γ N) 0 * Omy μ (γ N) - relativePosition μ (γ N) 1 * Omx μ (γ N))) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hneg'
  obtain ⟨u, hu1, hu2⟩ := ((left_gt_of_deriv_neg hd hdneg).and
    (Ioo_mem_nhdsLT hNt)).exists
  have := hbefore u ⟨hu2.1.le, hu2.2⟩
  rw [hN0] at hu1
  linarith

-- ===== Solutions.CM30 =====
/-- `Ω_x` as a function of the physical position relative to the primary. -/
noncomputable def om (μ X Y : ℝ) : ℝ :=
  (X - μ) - (1 - μ) * (X - μ + μ) / Real.sqrt ((X - μ + μ) ^ 2 + Y ^ 2) ^ 3 -
    μ * (X - μ - 1 + μ) / Real.sqrt ((X - μ - 1 + μ) ^ 2 + Y ^ 2) ^ 3

lemma Omx_eq_om (μ : ℝ) (s : Phase) :
    Omx μ s = om μ (relativePosition μ s 0) (relativePosition μ s 1) := by
  rw [(relPos_eq μ s).1, (relPos_eq μ s).2]; rfl

/-- The mixed second derivative `Ω_{xy}` at a physical position. -/
noncomputable def omXY (μ X Y : ℝ) : ℝ :=
  3 * (1 - μ) * X * Y / Real.sqrt ((X - μ + μ) ^ 2 + Y ^ 2) ^ 5 +
    3 * μ * (X - 1) * Y / Real.sqrt ((X - μ - 1 + μ) ^ 2 + Y ^ 2) ^ 5

lemma omXY_pos (μ X Y : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hX : X ≤ 0) (hY : Y < 0) :
    0 < omXY μ X Y := by
  unfold omXY
  have hY2 : 0 < Y ^ 2 := by nlinarith
  have h1 : 0 < Real.sqrt ((X - μ + μ) ^ 2 + Y ^ 2) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 < Real.sqrt ((X - μ - 1 + μ) ^ 2 + Y ^ 2) := Real.sqrt_pos.2 (by positivity)
  have a1 : 0 ≤ 3 * (1 - μ) * X * Y := by
    have : 0 ≤ X * Y := by nlinarith
    have : 0 < 3 * (1 - μ) := by linarith
    nlinarith
  have a2 : 0 < 3 * μ * (X - 1) * Y := by
    have : 0 < (X - 1) * Y := by nlinarith
    have : 0 < 3 * μ := by linarith
    nlinarith
  have := div_nonneg a1 (pow_pos h1 5).le
  have := div_pos a2 (pow_pos h2 5)
  linarith

/-- Chain rule for `Ω_x` along a curve with vanishing horizontal velocity. -/
lemma om_hasDerivAt (μ : ℝ) {X Y : ℝ → ℝ} {b t : ℝ} (hX : HasDerivAt X 0 t)
    (hY : HasDerivAt Y b t) (h1 : 0 < (X t) ^ 2 + (Y t) ^ 2)
    (h2 : 0 < (X t - 1) ^ 2 + (Y t) ^ 2) :
    HasDerivAt (fun u => om μ (X u) (Y u)) (b * omXY μ (X t) (Y t)) t := by
  have e1 : ∀ u, (X u - μ + μ) = X u := fun u => by ring
  have e2 : ∀ u, (X u - μ - 1 + μ) = X u - 1 := fun u => by ring
  have hn1 : HasDerivAt (fun u => X u - μ + μ) 0 t := by
    have := (hX.sub_const μ).add_const μ; simpa using this
  have hn2 : HasDerivAt (fun u => X u - μ - 1 + μ) 0 t := by
    have := ((hX.sub_const μ).sub_const 1).add_const μ; simpa using this
  have hq1 := ((hn1.mul hn1).add (hY.mul hY)).congr_of_eventuallyEq
    (f₁ := fun u => (X u - μ + μ) ^ 2 + Y u ^ 2) (Eventually.of_forall fun u => by simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]; ring)
  have hq2 := ((hn2.mul hn2).add (hY.mul hY)).congr_of_eventuallyEq
    (f₁ := fun u => (X u - μ - 1 + μ) ^ 2 + Y u ^ 2) (Eventually.of_forall fun u => by simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]; ring)
  have hq1' : ((X t - μ + μ) ^ 2 + Y t ^ 2) ≠ 0 := by rw [e1]; exact h1.ne'
  have hq2' : ((X t - μ - 1 + μ) ^ 2 + Y t ^ 2) ≠ 0 := by rw [e2]; exact h2.ne'
  have hr1 := hq1.sqrt hq1'
  have hr2 := hq2.sqrt hq2'
  have hs1 := ((hr1.mul hr1).mul hr1).congr_of_eventuallyEq
    (f₁ := fun u => Real.sqrt ((X u - μ + μ) ^ 2 + Y u ^ 2) ^ 3)
    (Eventually.of_forall fun u => by simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]; ring)
  have hs2 := ((hr2.mul hr2).mul hr2).congr_of_eventuallyEq
    (f₁ := fun u => Real.sqrt ((X u - μ - 1 + μ) ^ 2 + Y u ^ 2) ^ 3)
    (Eventually.of_forall fun u => by simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]; ring)
  have hr1p : 0 < Real.sqrt ((X t - μ + μ) ^ 2 + Y t ^ 2) := Real.sqrt_pos.2 (by rw [e1]; exact h1)
  have hr2p : 0 < Real.sqrt ((X t - μ - 1 + μ) ^ 2 + Y t ^ 2) :=
    Real.sqrt_pos.2 (by rw [e2]; exact h2)
  have hd1 := (hn1.div hs1 (pow_pos hr1p 3).ne').const_mul (1 - μ)
  have hd2 := (hn2.div hs2 (pow_pos hr2p 3).ne').const_mul μ
  have htot := ((hX.sub_const μ).sub hd1).sub hd2
  have hfun : (fun u => om μ (X u) (Y u)) = fun u =>
      (X u - μ) - (1 - μ) * ((X u - μ + μ) / Real.sqrt ((X u - μ + μ) ^ 2 + Y u ^ 2) ^ 3) -
        μ * ((X u - μ - 1 + μ) / Real.sqrt ((X u - μ - 1 + μ) ^ 2 + Y u ^ 2) ^ 3) := by
    funext u; unfold om; ring
  rw [hfun]
  refine htot.congr_deriv ?_
  unfold omXY
  simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Pi.sub_apply]
  set r1 := Real.sqrt ((X t - μ + μ) ^ 2 + Y t ^ 2)
  set r2 := Real.sqrt ((X t - μ - 1 + μ) ^ 2 + Y t ^ 2)
  field_simp
  ring

/-- `Ω_x` along the flow, at a time with vanishing horizontal velocity. -/
lemma omx_hasDerivAt (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ)
    (hP : 0 < zNormSq ((φ t x : LeftEnergyState μ c) : Phase))
    (hD : 0 < secondCollisionDistanceSq ((φ t x : LeftEnergyState μ c) : Phase))
    (hV : Vx ((φ t x : LeftEnergyState μ c) : Phase) = 0) :
    HasDerivAt (fun u => Omx μ ((φ u x : LeftEnergyState μ c) : Phase))
      (Yd μ ((φ t x : LeftEnergyState μ c) : Phase) *
        omXY μ (relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0)
          (relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1)) t := by
  have hX := xrel_hasDerivAt' μ c φ hφ x t
  have hP' := hP; unfold zNormSq at hP'
  rw [XRd_eq _ hP'.ne', hV, mul_zero] at hX
  have hY := y_hasDerivAt μ c φ hφ x t
  have hfun : (fun u => Omx μ ((φ u x : LeftEnergyState μ c) : Phase)) = fun u =>
      om μ (relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0)
        (relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 1) :=
    funext fun u => Omx_eq_om μ _
  rw [hfun]
  apply om_hasDerivAt μ hX hY
  · rw [(relPos_eq μ _).1, (relPos_eq μ _).2]
    have : (2 * (((φ t x : LeftEnergyState μ c) : Phase) 0 ^ 2 -
        ((φ t x : LeftEnergyState μ c) : Phase) 1 ^ 2)) ^ 2 +
        (4 * ((φ t x : LeftEnergyState μ c) : Phase) 0 * ((φ t x : LeftEnergyState μ c) : Phase) 1) ^ 2 =
        4 * (((φ t x : LeftEnergyState μ c) : Phase) 0 ^ 2 +
          ((φ t x : LeftEnergyState μ c) : Phase) 1 ^ 2) ^ 2 := by ring
    rw [this]; positivity
  · rw [(relPos_eq μ _).1, (relPos_eq μ _).2]
    unfold secondCollisionDistanceSq at hD; exact hD

set_option maxHeartbeats 4000000 in
/-- Birkhoff's third-derivative lemma: along the flow, with `x₁ ≤ 0`, `x₂ < 0`, the horizontal
velocity cannot have a local minimum `0` at a time where `v₂ ≤ 0`. -/
theorem vx_no_touch_down (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (x : LeftEnergyState μ c) (M : ℝ)
    (hP : 0 < zNormSq ((φ M x : LeftEnergyState μ c) : Phase))
    (hX : relativePosition μ ((φ M x : LeftEnergyState μ c) : Phase) 0 ≤ 0)
    (hY : relativePosition μ ((φ M x : LeftEnergyState μ c) : Phase) 1 < 0)
    (hV : Vx ((φ M x : LeftEnergyState μ c) : Phase) = 0)
    (hVy : Vy μ ((φ M x : LeftEnergyState μ c) : Phase) ≤ 0)
    (hmin : ∀ᶠ u in 𝓝 M, 0 ≤ Vx ((φ u x : LeftEnergyState μ c) : Phase)) : False := by
  set γ : ℝ → Phase := fun u => ((φ u x : LeftEnergyState μ c) : Phase) with hγ
  have hγc : Continuous γ :=
    continuous_subtype_val.comp (φ.continuous continuous_id continuous_const)
  have hPev : ∀ᶠ u in 𝓝 M, 0 < zNormSq (γ u) :=
    (cont_zNormSq.comp hγc).continuousAt.eventually (Ioi_mem_nhds hP)
  have hVxd := vx_hasDerivAt μ c φ hφ x M hP
  -- `v₁` has a local minimum `0`, so `Ω_x = 2 v₂`
  have hlm : IsLocalMin (fun u => Vx (γ u)) M := by
    filter_upwards [hmin] with u hu; show Vx (γ M) ≤ Vx (γ u); rw [hV]; exact hu
  have h0 := hlm.hasDerivAt_eq_zero hVxd
  have hF0 : Omx μ (γ M) - 2 * Vy μ (γ M) = 0 := by
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · exact h
  -- `F = Ω_x - 2 v₂` is strictly decreasing at `M`
  have hD := comp_D_pos _ (φ M x).2
  have hOm := omx_hasDerivAt μ c φ hφ x M hP hD hV
  have hVyd := vy_hasDerivAt μ c φ hφ x M hP
  have hF := hOm.sub (hVyd.const_mul 2)
  have hP' := hP; unfold zNormSq at hP'
  have hOmy := omega_y_pos μ c hμ0 hμ1 hc (γ M) (φ M x).2 (by rwa [(relPos_eq μ _).2] at hY)
  have hB := omXY_pos μ _ _ hμ0 hμ1 hX hY
  have hFneg : Yd μ (γ M) * omXY μ (relativePosition μ (γ M) 0) (relativePosition μ (γ M) 1) -
      2 * (4 * zNormSq (γ M) * (2 * Vx (γ M) + Omy μ (γ M))) < 0 := by
    rw [Yd_eq μ _ hP'.ne', hV]
    have : 4 * (γ M 0 ^ 2 + γ M 1 ^ 2) * Vy μ (γ M) *
        omXY μ (relativePosition μ (γ M) 0) (relativePosition μ (γ M) 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hVy) hB.le
    have : 0 < 2 * (4 * zNormSq (γ M) * (2 * 0 + Omy μ (γ M))) := by
      have := hP; positivity
    linarith
  -- so `F > 0` just before `M`, where `v₁` then increases to `0`
  -- on `[u', M]` for `u'` close enough, `F > 0` and `P > 0`
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hPev
  have hFev : ∀ᶠ v in 𝓝[<] M, 0 < Omx μ (γ v) - 2 * Vy μ (γ v) := by
    filter_upwards [left_gt_of_deriv_neg hF hFneg] with v hv
    simp only [Pi.sub_apply] at hv; rw [hF0] at hv; exact hv
  obtain ⟨a, ha, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (hFev.and (nhdsWithin_le_nhds hPev))
  set w := max a (M - ε / 2) with hw
  have hwM : w < M := max_lt ha (by linarith)
  set v := (w + M) / 2 with hv
  have hvI : v ∈ Ioo w M := ⟨by linarith, by linarith⟩
  have hmono : StrictMonoOn (fun r => Vx (γ r)) (Icc v M) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro r hr
      have hPr : 0 < zNormSq (γ r) := hball (by
        rw [Real.dist_eq, abs_lt]; constructor <;>
          linarith [hr.1, hr.2, le_max_right a (M - ε / 2)])
      exact (vx_hasDerivAt μ c φ hφ x r hPr).continuousAt.continuousWithinAt
    · intro r hr; rw [interior_Icc] at hr
      have hr' : r ∈ Ioo a M := ⟨by linarith [hr.1, le_max_left a (M - ε / 2)], hr.2⟩
      obtain ⟨hFr, hPr⟩ := hsub hr'
      rw [(vx_hasDerivAt μ c φ hφ x r hPr).deriv]
      positivity
  have hlt := hmono ⟨le_refl _, by linarith⟩ ⟨by linarith, le_refl _⟩ hvI.2
  simp only at hlt; rw [hV] at hlt
  -- but `v₁ ≥ 0` near `M`
  obtain ⟨δ, hδ, hball2⟩ := Metric.eventually_nhds_iff.1 hmin
  have : 0 ≤ Vx (γ v) := by
    by_cases hvd : dist v M < δ
    · exact hball2 hvd
    · exfalso
      -- shrink: pick a point closer to `M` on the same increasing stretch
      push Not at hvd
      set v' := max v (M - δ / 2) with hv'
      have hv'I : v' ∈ Icc v M := ⟨le_max_left _ _, max_le hvI.2.le (by linarith)⟩
      have hv'M : v' < M := max_lt hvI.2 (by linarith)
      have h1 := hmono hv'I ⟨by linarith [hv'I.1], le_refl _⟩ hv'M
      simp only at h1; rw [hV] at h1
      have h2 := hball2 (show dist v' M < δ by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [le_max_right v (M - δ / 2)])
      linarith
  linarith

-- ===== Solutions.CM31 =====
/-- On the vertical line through the primary, below or above the axis, `Ω_x < 0`. -/
lemma omx_on_line (μ : ℝ) (hμ0 : 0 < μ) (s : Phase) (hX : relativePosition μ s 0 = 0)
    (hY : relativePosition μ s 1 ≠ 0) : Omx μ s < 0 := by
  rw [Omx_eq_om, hX]
  set Y := relativePosition μ s 1
  unfold om
  have e1 : ((0:ℝ) - μ + μ) = 0 := by ring
  have e2 : ((0:ℝ) - μ - 1 + μ) = -1 := by ring
  rw [e1, e2]
  have hR : 1 < Real.sqrt ((-1) ^ 2 + Y ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]; have : 0 < Y ^ 2 := by positivity
    nlinarith
  have h3 : 1 < Real.sqrt ((-1) ^ 2 + Y ^ 2) ^ 3 := one_lt_pow₀ hR (by norm_num)
  have : μ * -1 / Real.sqrt ((-1) ^ 2 + Y ^ 2) ^ 3 > -μ := by
    rw [gt_iff_lt, lt_div_iff₀ (by linarith)]; nlinarith
  simp only [mul_zero, zero_div, sub_zero]
  linarith

/-- If `v₁ ≡ 0` near a time, then `Ω_x = 2 v₂` there. -/
lemma omx_eq_of_vx_const (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (s : ℝ)
    (hP : 0 < zNormSq ((φ s x : LeftEnergyState μ c) : Phase))
    (h0 : ∀ᶠ u in 𝓝 s, Vx ((φ u x : LeftEnergyState μ c) : Phase) = 0) :
    Omx μ ((φ s x : LeftEnergyState μ c) : Phase) =
      2 * Vy μ ((φ s x : LeftEnergyState μ c) : Phase) := by
  have hd := vx_hasDerivAt μ c φ hφ x s hP
  have hd' : HasDerivAt (fun u => Vx ((φ u x : LeftEnergyState μ c) : Phase)) 0 s :=
    (hasDerivAt_const s (0:ℝ)).congr_of_eventuallyEq h0
  have := hd.unique hd'
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

set_option maxHeartbeats 8000000 in
/-- A forward orbit cannot stay forever in `{x₁ < 0, x₂ < 0, v₁ > 0}` with nonnegative
angular momentum about the primary. -/
theorem far_no_infinite_stay2 (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (x : LeftEnergyState μ c)
    (hq : ∀ t > 0,
      relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0 < 0 ∧
      relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0 ∧
      0 < Vx ((φ t x : LeftEnergyState μ c) : Phase) ∧
      0 ≤ Lpoly μ ((φ t x : LeftEnergyState μ c) : Phase)) : False := by
  have hK := left_energy_component_compact μ c hμ0 hμ1 hc
  set X : ℝ → ℝ := fun t => relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0 with hX
  have hP : ∀ t > 0, 0 < zNormSq ((φ t x : LeftEnergyState μ c) : Phase) := by
    intro t ht
    have hy := (hq t ht).2.1; rw [(relPos_eq μ _).2] at hy
    have : ((φ t x : LeftEnergyState μ c) : Phase) 0 ≠ 0 := by rintro h0; rw [h0] at hy; simp at hy
    unfold zNormSq; positivity
  have hXd : ∀ t, HasDerivAt X (XRd ((φ t x : LeftEnergyState μ c) : Phase)) t :=
    fun t => xrel_hasDerivAt' μ c φ hφ x t
  have hXdpos : ∀ t > 0, 0 < XRd ((φ t x : LeftEnergyState μ c) : Phase) := by
    intro t ht
    have hPt := hP t ht; have hPt' := hPt; unfold zNormSq at hPt'
    rw [XRd_eq _ hPt'.ne']
    have := (hq t ht).2.2.1
    unfold zNormSq at hPt; positivity
  have hXmono : StrictMonoOn X (Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
      (fun t _ => (hXd t).continuousAt.continuousWithinAt)
    intro t ht; rw [interior_Ioi] at ht; rw [(hXd t).deriv]; exact hXdpos t ht
  set Xl := sSup (X '' Ioi 0) with hXldef
  have hbdd : BddAbove (X '' Ioi 0) := ⟨0, by rintro _ ⟨t, ht, rfl⟩; exact (hq t ht).1.le⟩
  have hne : (X '' Ioi 0).Nonempty := ⟨X 1, 1, by norm_num, rfl⟩
  have hXle : ∀ t > 0, X t ≤ Xl := fun t ht => le_csSup hbdd ⟨t, ht, rfl⟩
  have hXl0 : Xl ≤ 0 := csSup_le hne (by rintro _ ⟨t, ht, rfl⟩; exact (hq t ht).1.le)
  have hXlim : Tendsto X atTop (𝓝 Xl) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨_, ⟨t0, ht0, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne (show Xl - ε < Xl by linarith)
    refine ⟨t0, fun t ht => ?_⟩
    have h1 : X t0 ≤ X t := by
      rcases eq_or_lt_of_le ht with h | h
      · rw [h]
      · exact (hXmono ht0 (lt_trans ht0 h) h).le
    have h2 := hXle t (lt_of_lt_of_le ht0 ht)
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  haveI : CompactSpace (LeftEnergyState μ c) := isCompact_iff_compactSpace.1 hK
  obtain ⟨p, -, ψ, hψ, hlim⟩ := isCompact_univ.tendsto_subseq
    (x := fun n : ℕ => (φ (n : ℝ) x : LeftEnergyState μ c)) (fun n => mem_univ _)
  have hψt : Tendsto (fun n => ((ψ n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop
  have horb : ∀ s, Tendsto (fun n => ((φ (s + (ψ n : ℝ)) x : LeftEnergyState μ c) : Phase)) atTop
      (𝓝 ((φ s p : LeftEnergyState μ c) : Phase)) := by
    intro s
    have hc1 : Continuous fun y : LeftEnergyState μ c => ((φ s y : LeftEnergyState μ c) : Phase) :=
      continuous_subtype_val.comp (φ.continuous continuous_const continuous_id)
    have := (hc1.tendsto p).comp hlim
    refine this.congr (fun n => ?_)
    simp only [Function.comp_apply]; rw [Flow.map_add]
  have hev : ∀ s, ∀ᶠ n in atTop, 0 < s + ((ψ n : ℕ) : ℝ) := fun s =>
    (tendsto_atTop_add_const_left _ s hψt).eventually (eventually_gt_atTop 0)
  have hXp : ∀ s, relativePosition μ ((φ s p : LeftEnergyState μ c) : Phase) 0 = Xl := by
    intro s
    have h1 := ((cont_relPos0 μ).tendsto _).comp (horb s)
    have h2 := hXlim.comp (tendsto_atTop_add_const_left _ s hψt)
    exact tendsto_nhds_unique h1 h2
  have hYp : ∀ s, relativePosition μ ((φ s p : LeftEnergyState μ c) : Phase) 1 ≤ 0 := by
    intro s
    exact le_of_tendsto (((cont_relPos1 μ).tendsto _).comp (horb s))
      ((hev s).mono fun n hn => (hq _ hn).2.1.le)
  have hLp : ∀ s, 0 ≤ Lpoly μ ((φ s p : LeftEnergyState μ c) : Phase) := by
    intro s
    exact ge_of_tendsto (((cont_Lpoly μ).tendsto _).comp (horb s))
      ((hev s).mono fun n hn => (hq _ hn).2.2.2)
  have hXRd0 : ∀ s, XRd ((φ s p : LeftEnergyState μ c) : Phase) = 0 := by
    intro s
    have h1 := xrel_hasDerivAt' μ c φ hφ p s
    have hfun : (fun u : ℝ => relativePosition μ ((φ u p : LeftEnergyState μ c) : Phase) 0) =
        fun _ => Xl := funext hXp
    rw [hfun] at h1
    exact h1.unique (hasDerivAt_const s Xl)
  by_cases hsome : ∃ s, 0 < zNormSq ((φ s p : LeftEnergyState μ c) : Phase)
  · obtain ⟨s, hs⟩ := hsome
    have hγc : Continuous fun u => ((φ u p : LeftEnergyState μ c) : Phase) :=
      continuous_subtype_val.comp (φ.continuous continuous_id continuous_const)
    have hPev : ∀ᶠ u in 𝓝 s, 0 < zNormSq ((φ u p : LeftEnergyState μ c) : Phase) :=
      ((cont_zNormSq.comp hγc).continuousAt).eventually (Ioi_mem_nhds hs)
    have hVx0 : ∀ u, 0 < zNormSq ((φ u p : LeftEnergyState μ c) : Phase) →
        Vx ((φ u p : LeftEnergyState μ c) : Phase) = 0 := by
      intro u hu
      have hu' := hu; unfold zNormSq at hu'
      have := hXRd0 u; rw [XRd_eq _ hu'.ne'] at this
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact h
    have hVxev : ∀ᶠ u in 𝓝 s, Vx ((φ u p : LeftEnergyState μ c) : Phase) = 0 :=
      hPev.mono fun u hu => hVx0 u hu
    have hF := omx_eq_of_vx_const μ c φ hφ p s hs hVxev
    have hs' := hs; unfold zNormSq at hs'
    rcases lt_or_eq_of_le (hYp s) with hYs | hYs
    · rcases le_or_gt (Vy μ ((φ s p : LeftEnergyState μ c) : Phase)) 0 with hVy | hVy
      · exact vx_no_touch_down μ c hμ0 hμ1 hc φ hφ p s hs (by rw [hXp]; exact hXl0) hYs
          (hVx0 s hs) hVy (hVxev.mono fun u hu => by rw [hu])
      · -- positive angular momentum forces the orbit onto the vertical line
        have hL := hLp s
        rw [Lpoly_eq μ _ hs'.ne', hVx0 s hs, hXp] at hL
        have hXl : Xl = 0 := by
          by_contra hne'
          have : Xl < 0 := lt_of_le_of_ne hXl0 hne'
          nlinarith
        have := omx_on_line μ hμ0 _ (by rw [hXp, hXl]) hYs.ne
        linarith
    · -- on the axis
      have hmax : IsLocalMax (fun u => relativePosition μ ((φ u p : LeftEnergyState μ c) : Phase) 1) s := by
        filter_upwards with u; rw [hYs]; exact hYp u
      have hYd := hmax.hasDerivAt_eq_zero (y_hasDerivAt μ c φ hφ p s)
      rw [Yd_eq μ _ hs'.ne'] at hYd
      have hVy0 : Vy μ ((φ s p : LeftEnergyState μ c) : Phase) = 0 := by
        rcases mul_eq_zero.1 hYd with h | h
        · linarith
        · exact h
      rw [hVy0, mul_zero] at hF
      have hy := hYs; rw [(relPos_eq μ _).2] at hy
      have hx := hXp s; rw [(relPos_eq μ _).1] at hx
      have hmq := (φ s p).2
      generalize ((φ s p : LeftEnergyState μ c) : Phase) = q at hy hx hmq hF hs'
      have hq0 : q 0 = 0 := by
        by_contra h0
        have : q 1 = 0 := by
          rcases mul_eq_zero.1 hy with h | h
          · rcases mul_eq_zero.1 h with h' | h'
            · norm_num at h'
            · exact absurd h' h0
          · exact h
        rw [this] at hx
        have : 0 < q 0 ^ 2 := by positivity
        linarith
      have hq1 : q 1 ≠ 0 := by intro h1; rw [hq0, h1] at hs'; simp at hs'
      have := far_axis_omega_x_pos μ c hμ0 hμ1 hc q hmq hq0 hq1
      linarith
  · push Not at hsome
    have hz : ∀ s, ((φ s p : LeftEnergyState μ c) : Phase) 0 = 0 ∧
        ((φ s p : LeftEnergyState μ c) : Phase) 1 = 0 := by
      intro s
      have := hsome s; unfold zNormSq at this
      constructor <;> nlinarith [sq_nonneg (((φ s p : LeftEnergyState μ c) : Phase) 0),
        sq_nonneg (((φ s p : LeftEnergyState μ c) : Phase) 1)]
    obtain ⟨h0, h1, -, -⟩ := flow_coords' μ c φ hφ p 0
    have hc0 : (fun u : ℝ => ((φ u p : LeftEnergyState μ c) : Phase) 0) = fun _ => 0 :=
      funext fun u => (hz u).1
    have hc1 : (fun u : ℝ => ((φ u p : LeftEnergyState μ c) : Phase) 1) = fun _ => 0 :=
      funext fun u => (hz u).2
    rw [hc0] at h0; rw [hc1] at h1
    have e0 := h0.unique (hasDerivAt_const 0 (0:ℝ))
    have e1 := h1.unique (hasDerivAt_const 0 (0:ℝ))
    obtain ⟨z0, z1⟩ := hz 0
    unfold Xa at e0; unfold Xb at e1
    rw [z0, z1] at e0 e1
    have hsp := collision_speed μ c _ (φ 0 p).2 z0 z1
    have : ((φ 0 p : LeftEnergyState μ c) : Phase) 2 = 0 := by linarith
    have : ((φ 0 p : LeftEnergyState μ c) : Phase) 3 = 0 := by linarith
    nlinarith

-- ===== Solutions.CM32 =====
/-- Before its crossing, a far arc lies strictly left of the vertical line. -/
lemma far_arc_X_neg (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (x : LeftEnergyState μ c) (τ : ℝ) (harc : IsFarShootingArc φ x τ) :
    ∀ t ∈ Ioo 0 τ, relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0 < 0 := by
  obtain ⟨hτ, hlow, hend, hcross, hvx⟩ := harc
  set γ : ℝ → Phase := fun u => ((φ u x : LeftEnergyState μ c) : Phase) with hγ
  have hPpos : ∀ t ∈ Ioc 0 τ, 0 < zNormSq (γ t) := by
    intro t ht
    have hy : relativePosition μ (γ t) 1 < 0 := by
      rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h]; exact hend
      · exact hlow t ⟨ht.1, h⟩
    rw [(relPos_eq μ _).2] at hy
    have : γ t 0 ≠ 0 := by rintro h0; rw [h0] at hy; simp at hy
    unfold zNormSq; positivity
  have hXd : ∀ t, HasDerivAt (fun u => relativePosition μ (γ u) 0) (XRd (γ t)) t :=
    fun t => xrel_hasDerivAt' μ c φ hφ x t
  intro t ht
  have hmono : StrictMonoOn (fun u => relativePosition μ (γ u) 0) (Icc t τ) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun u _ => (hXd u).continuousAt.continuousWithinAt)
    intro u hu; rw [interior_Icc] at hu
    have hu' : u ∈ Ioc 0 τ := ⟨by linarith [ht.1, hu.1], hu.2.le⟩
    have hP := hPpos u hu'; have hP' := hP; unfold zNormSq at hP'
    rw [(hXd u).deriv, XRd_eq _ hP'.ne']
    have := hvx u hu'; rw [(jv_eq μ _).1] at this
    unfold zNormSq at hP; positivity
  have := hmono ⟨le_refl _, ht.2.le⟩ ⟨ht.2.le, le_refl _⟩ ht.2
  simp only at this; rw [hcross] at this; exact this

/-- A sign condition holding frequently along the family passes to the limit orbit. -/
lemma freq_limit_nonpos {μ c : ℝ} (φ : Flow ℝ (LeftEnergyState μ c))
    (Sx : ℝ → LeftEnergyState μ c) (b : ℝ) (hS : ContinuousAt Sx b) (f : Phase → ℝ)
    (hf : Continuous f) (t : ℝ)
    (h : ∃ᶠ r in 𝓝[<] b, f ((φ t (Sx r) : LeftEnergyState μ c) : Phase) ≤ 0) :
    f ((φ t (Sx b) : LeftEnergyState μ c) : Phase) ≤ 0 := by
  have hc := flow_state_continuousAt φ Sx b hS 1 t
  have hc' : ContinuousAt (fun r : ℝ => f ((φ t (Sx r) : LeftEnergyState μ c) : Phase)) b := by
    have h2 : ContinuousAt (fun r : ℝ => (t, r)) b := by fun_prop
    have := (hf.continuousAt).comp (hc.comp h2)
    simpa [Function.comp_def] using this
  by_contra hpos; push Not at hpos
  have hev := nhdsWithin_le_nhds (s := Iio b) (hc'.eventually (Ioi_mem_nhds hpos))
  obtain ⟨r, h1, h2⟩ := (h.and_eventually hev).exists
  exact absurd h1 (not_le.2 h2)

set_option maxHeartbeats 8000000 in
/-- At a vertical-tangency end of the far limit orbit, the arc lengths cannot overshoot:
otherwise the limit orbit would slide along the vertical line with `v₁ ≡ 0`, which forces
`Ω_x = 2 v₂ > 0` there, while `Ω_x < 0` on that line. -/
lemma far_tangency_upper (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (b : ℝ) (hb : 0 < b) (Sx : ℝ → LeftEnergyState μ c) (hSxc : ContinuousAt Sx b)
    {xb : LeftEnergyState μ c} (hSxb : Sx b = xb)
    (hSxr : ∀ r ∈ Ioo (b / 2) b, ∀ x : LeftEnergyState μ c,
      (x : Phase) = farShootingStart μ c r → x = Sx r)
    (hgood : ∀ r ∈ Set.Ioo 0 b, ∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c r ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ)
    (S : ℝ) (hS0 : 0 < S) (hX : relativePosition μ ((φ S xb : LeftEnergyState μ c) : Phase) 0 = 0)
    (hY : relativePosition μ ((φ S xb : LeftEnergyState μ c) : Phase) 1 < 0) (h : ℝ) (hh : 0 < h) :
    ∀ᶠ r in 𝓝[<] b, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
      (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ → τ ≤ S + h := by
  set γ : ℝ → Phase := fun u => ((φ u xb : LeftEnergyState μ c) : Phase) with hγ
  have hγc : Continuous γ :=
    continuous_subtype_val.comp (φ.continuous continuous_id continuous_const)
  have hYc : Continuous fun u => relativePosition μ (γ u) 1 := (cont_relPos1 μ).comp hγc
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    (hYc.continuousAt.eventually (Iio_mem_nhds (show relativePosition μ (γ S) 1 < 0 from hY)))
  set h' := min h (ε / 2) with hh'
  have hh'0 : 0 < h' := lt_min hh (half_pos hε)
  have hh'h : h' ≤ h := min_le_left _ _
  have hh'ε : h' ≤ ε / 2 := min_le_right _ _
  have hYneg : ∀ u ∈ Icc S (S + h'), relativePosition μ (γ u) 1 < 0 := by
    intro u hu; apply hball; rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2]
  have hPpos : ∀ u ∈ Icc S (S + h'), 0 < zNormSq (γ u) := by
    intro u hu
    have hy := hYneg u hu; rw [(relPos_eq μ _).2] at hy
    have : γ u 0 ≠ 0 := by rintro h0; rw [h0] at hy; simp at hy
    unfold zNormSq; positivity
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq := hcon.and_eventually (Ioo_mem_nhdsLT (half_lt_self hb))
  have hlong : ∀ t ∈ Icc S (S + h'), ∃ᶠ r in 𝓝[<] b,
      relativePosition μ ((φ t (Sx r) : LeftEnergyState μ c) : Phase) 0 < 0 ∧
      0 < XRd ((φ t (Sx r) : LeftEnergyState μ c) : Phase) := by
    intro t ht
    refine hfreq.mono fun r ⟨hnot, hr⟩ => ?_
    push Not at hnot
    obtain ⟨x, τ, hx, harc, hτ⟩ := hnot
    rw [hSxr r hr x hx] at harc
    have htτ : t ∈ Ioo 0 τ := ⟨lt_of_lt_of_le hS0 ht.1, by linarith [ht.2]⟩
    refine ⟨far_arc_X_neg μ c φ hφ (Sx r) τ harc t htτ, ?_⟩
    obtain ⟨-, hlow, -, -, hvx⟩ := harc
    have hy := hlow t htτ; rw [(relPos_eq μ _).2] at hy
    have hP : 0 < ((φ t (Sx r) : LeftEnergyState μ c) : Phase) 0 ^ 2 +
        ((φ t (Sx r) : LeftEnergyState μ c) : Phase) 1 ^ 2 := by
      have : ((φ t (Sx r) : LeftEnergyState μ c) : Phase) 0 ≠ 0 := by
        rintro h0; rw [h0] at hy; simp at hy
      positivity
    rw [XRd_eq _ hP.ne']
    have := hvx t ⟨htτ.1, htτ.2.le⟩; rw [(jv_eq μ _).1] at this
    positivity
  have hXle : ∀ t ∈ Icc S (S + h'), relativePosition μ (γ t) 0 ≤ 0 := by
    intro t ht
    have := freq_limit_nonpos φ Sx b hSxc (fun s => relativePosition μ s 0) (cont_relPos0 μ) t
      ((hlong t ht).mono fun r hr => hr.1.le)
    rw [hSxb] at this; exact this
  have hXRd : ∀ t ∈ Icc S (S + h'), 0 ≤ XRd (γ t) := by
    intro t ht
    have := freq_limit_nonpos φ Sx b hSxc (fun s => -XRd s) cont_XRd.neg t
      ((hlong t ht).mono fun r hr => by show -XRd _ ≤ 0; linarith [hr.2])
    rw [hSxb] at this; linarith
  -- so `x₁ ≡ 0` on `[S, S + h']`
  have hXd : ∀ t, HasDerivAt (fun u => relativePosition μ (γ u) 0) (XRd (γ t)) t :=
    fun t => xrel_hasDerivAt' μ c φ hφ xb t
  have hmono : MonotoneOn (fun u => relativePosition μ (γ u) 0) (Icc S (S + h')) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun u _ => (hXd u).continuousAt.continuousWithinAt)
      (fun u _ => (hXd u).differentiableAt.differentiableWithinAt)
    intro u hu; rw [interior_Icc] at hu; rw [(hXd u).deriv]; exact hXRd u ⟨hu.1.le, hu.2.le⟩
  have hX0 : ∀ u ∈ Icc S (S + h'), relativePosition μ (γ u) 0 = 0 := by
    intro u hu
    have := hmono ⟨le_refl _, by linarith⟩ hu hu.1
    simp only at this
    rw [show relativePosition μ (γ S) 0 = 0 from hX] at this
    exact le_antisymm (hXle u hu) this
  have hVx0 : ∀ u ∈ Ioo S (S + h'), Vx (γ u) = 0 := by
    intro u hu
    have hev : (fun v => relativePosition μ (γ v) 0) =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv; exact hX0 v ⟨hv.1.le, hv.2.le⟩
    have := (hXd u).unique ((hasDerivAt_const u (0:ℝ)).congr_of_eventuallyEq hev)
    have hP := hPpos u ⟨hu.1.le, hu.2.le⟩; have hP' := hP; unfold zNormSq at hP'
    rw [XRd_eq _ hP'.ne'] at this
    unfold zNormSq at hP
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact h1
  set t1 := S + h' / 2 with ht1
  have ht1I : t1 ∈ Ioo S (S + h') := ⟨by linarith, by linarith⟩
  have hP1 := hPpos t1 ⟨ht1I.1.le, ht1I.2.le⟩
  have hFeq : ∀ u ∈ Ioo S (S + h'), Omx μ (γ u) = 2 * Vy μ (γ u) := by
    intro u hu
    exact omx_eq_of_vx_const μ c φ hφ xb u (hPpos u ⟨hu.1.le, hu.2.le⟩)
      (by filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv; exact hVx0 v hv)
  have hOm := omx_hasDerivAt μ c φ hφ xb t1 hP1 (comp_D_pos _ (φ t1 xb).2) (hVx0 t1 ht1I)
  have hVyd := vy_hasDerivAt μ c φ hφ xb t1 hP1
  have hF := hOm.sub (hVyd.const_mul 2)
  have hF0 : HasDerivAt ((fun u => Omx μ ((φ u xb : LeftEnergyState μ c) : Phase)) -
      fun y => 2 * Vy μ ((φ y xb : LeftEnergyState μ c) : Phase)) 0 t1 :=
    (hasDerivAt_const t1 (0:ℝ)).congr_of_eventuallyEq (by
      filter_upwards [Ioo_mem_nhds ht1I.1 ht1I.2] with v hv
      simp only [Pi.sub_apply]; have := hFeq v hv; simp only [hγ] at this; linarith)
  have heq := hF.unique hF0
  have hP1' := hP1; unfold zNormSq at hP1'
  have hY1 := hYneg t1 ⟨ht1I.1.le, ht1I.2.le⟩
  have hB := omXY_pos μ _ _ hμ0 hμ1 (hX0 t1 ⟨ht1I.1.le, ht1I.2.le⟩).le hY1
  have hOmy := omega_y_pos μ c hμ0 hμ1 hc (γ t1) (φ t1 xb).2 (by rwa [(relPos_eq μ _).2] at hY1)
  rw [Yd_eq μ _ hP1'.ne', hVx0 t1 ht1I] at heq
  have hVy : 0 < Vy μ (γ t1) := by
    by_contra hle; push Not at hle
    have : 4 * (γ t1 0 ^ 2 + γ t1 1 ^ 2) * Vy μ (γ t1) *
        omXY μ (relativePosition μ (γ t1) 0) (relativePosition μ (γ t1) 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hle) hB.le
    have : 0 < 2 * (4 * zNormSq (γ t1) * (2 * 0 + Omy μ (γ t1))) := by positivity
    linarith
  have hOmpos : 0 < Omx μ (γ t1) := by rw [hFeq t1 ht1I]; linarith
  have := omx_on_line μ hμ0 (γ t1) (hX0 t1 ⟨ht1I.1.le, ht1I.2.le⟩) hY1.ne
  linarith

-- ===== Solutions.CM33 =====
theorem far_arc_limit_rest (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (b : ℝ) (hb : 0 < b)
    (hgood : ∀ r ∈ Set.Ioo 0 b, ∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c r ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ)
    (hbad : ¬ (∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c b ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ)) :
    ∃ xb : LeftEnergyState μ c, (xb : Phase) = farShootingStart μ c b ∧
      jacobiVelocity (leviCivitaToJacobi μ (xb : Phase)) 1 < 0 ∧ ∃ T : ℝ, 0 < T ∧
      (∀ t ∈ Set.Ioo 0 T, relativePosition μ ((φ t xb : LeftEnergyState μ c) : Phase) 1 ≤ 0) ∧
      (∀ t ∈ Set.Ioo 0 T, 0 < jacobiVelocity (leviCivitaToJacobi μ ((φ t xb : LeftEnergyState μ c) : Phase)) 0) ∧
      (∀ t ∈ Set.Ioo 0 T, 0 < zNormSq ((φ t xb : LeftEnergyState μ c) : Phase)) ∧
      relativePosition μ ((φ T xb : LeftEnergyState μ c) : Phase) 0 = 0 ∧ relativePosition μ ((φ T xb : LeftEnergyState μ c) : Phase) 1 ≤ 0 ∧
      0 ≤ jacobiVelocity (leviCivitaToJacobi μ ((φ T xb : LeftEnergyState μ c) : Phase)) 0 ∧
      ∀ η > 0, ∃ δ > 0, ∀ r ∈ Set.Ioo (b - δ) b, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
        (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ → |τ - T| < η
 := by
  have hgood' : ∀ r ∈ Ioo 0 b, farShootingStart μ c r ∈ leftEnergyComponent μ c := by
    intro r hr; obtain ⟨x, hx, -⟩ := hgood r hr; rw [← hx]; exact x.2
  have hmemb := far_start_limit_mem μ c hμ0 hμ1 hc b hb hgood'
  set xb : LeftEnergyState μ c := ⟨farShootingStart μ c b, hmemb⟩ with hxbdef
  have hxb : (xb : Phase) = farShootingStart μ c b := rfl
  have hb0 : (xb : Phase) 0 = 0 := by rw [hxb]; simp [farShootingStart]
  have hb1 : (xb : Phase) 1 = b := by rw [hxb]; simp [farShootingStart]
  have hb3 : (xb : Phase) 3 = 0 := by rw [hxb]; simp [farShootingStart]
  have hv := far_start_moving μ c hμ0 hμ1 hc φ hφ b hb hgood xb hxb
  have hno : ¬ ∃ τ, IsFarShootingArc φ xb τ := fun h => hbad ⟨xb, hxb, h⟩
  obtain ⟨Sx, hSxb, hSxc, hSx⟩ := far_family μ c b hb xb hxb hgood'
  have hSxr : ∀ r ∈ Ioo (b / 2) b, ∀ x : LeftEnergyState μ c,
      (x : Phase) = farShootingStart μ c r → x = Sx r := by
    intro r hr x hx; exact Subtype.ext (by rw [hx, hSx r ⟨hr.1.le, hr.2.le⟩])
  -- Birkhoff's identity (59): nonnegative angular momentum along the good arcs
  have hLarc : ∀ x : LeftEnergyState μ c, ∀ τ : ℝ, IsFarShootingArc φ x τ →
      ∀ t ∈ Ioc 0 τ, 0 ≤ Lpoly μ ((φ t x : LeftEnergyState μ c) : Phase) :=
    fun x τ harc => far_arc_L_nonneg μ c hμ0 hμ1 hc φ hφ x τ harc
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → Phase, γ = fun u => ((φ u xb : LeftEnergyState μ c) : Phase) :=
    ⟨_, rfl⟩
  have hγd : ∀ u, γ u = ((φ u xb : LeftEnergyState μ c) : Phase) := fun u => by rw [hγ]
  have hγ0 : γ 0 = (xb : Phase) := by rw [hγd]; simp
  have hγc : Continuous γ := by
    rw [hγ]; exact continuous_subtype_val.comp (φ.continuous continuous_id continuous_const)
  have hmem : ∀ u, γ u ∈ leftEnergyComponent μ c := fun u => by rw [hγd]; exact (φ u xb).2
  set X : ℝ → ℝ := fun t => relativePosition μ (γ t) 0 with hX
  set Y : ℝ → ℝ := fun t => relativePosition μ (γ t) 1 with hY
  have hXc : Continuous X := (cont_relPos0 μ).comp hγc
  have hYc : Continuous Y := (cont_relPos1 μ).comp hγc
  have hX0 : X 0 < 0 := by simp only [hX]; rw [hγ0, (relPos_eq μ _).1, hb0, hb1]; nlinarith
  -- arcs near `b` outlast any time interval on which the limit orbit stays left of the line
  have hlong : ∀ T' > 0, (∀ t ∈ Icc 0 T', X t < 0) →
      ∀ᶠ r in 𝓝[<] b, r ∈ Ioo (b / 2) b ∧ ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
        (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ → T' < τ := by
    intro T' hT' hneg
    have htube := tube_pos φ Sx b hSxc (fun s => -relativePosition μ s 0) (cont_relPos0 μ).neg 0 T'
      (by intro t ht; rw [hSxb, ← hγd]; have := hneg t ht; simp only [hX] at this; linarith)
    filter_upwards [Ioo_mem_nhdsLT (half_lt_self hb), nhdsWithin_le_nhds htube] with r hr htr
    refine ⟨hr, fun x τ hx harc => ?_⟩
    rw [hSxr r hr x hx] at harc
    obtain ⟨hτ, -, -, hcross, -⟩ := harc
    by_contra hle; push Not at hle
    have := htr τ ⟨hτ.le, hle⟩
    rw [hcross] at this; simp at this
  have hlimit : ∀ T' > 0, (∀ t ∈ Icc 0 T', X t < 0) → ∀ t ∈ Ioo 0 T',
      Y t ≤ 0 ∧ 0 ≤ Lpoly μ (γ t) ∧ 0 ≤ XRd (γ t) := by
    intro T' hT' hneg t ht
    have hl := hlong T' hT' hneg
    have key : ∀ᶠ r in 𝓝[<] b,
        relativePosition μ ((φ t (Sx r) : LeftEnergyState μ c) : Phase) 1 < 0 ∧
        0 ≤ Lpoly μ ((φ t (Sx r) : LeftEnergyState μ c) : Phase) ∧
        0 < XRd ((φ t (Sx r) : LeftEnergyState μ c) : Phase) := by
      filter_upwards [hl] with r ⟨hr, hlr⟩
      obtain ⟨x, hx, τ, harc⟩ := hgood r ⟨lt_trans (half_pos hb) hr.1, hr.2⟩
      have hτ := hlr x τ hx harc
      have hfv := hLarc x τ harc t ⟨ht.1, by linarith [ht.2]⟩
      rw [hSxr r hr x hx] at harc hfv
      obtain ⟨-, hlow, -, -, hvx⟩ := harc
      have hy := hlow t ⟨ht.1, by linarith [ht.2]⟩
      have hvx' := hvx t ⟨ht.1, by linarith [ht.2]⟩
      rw [(jv_eq μ _).1] at hvx'
      have hy' := hy; rw [(relPos_eq μ _).2] at hy'
      have hP : 0 < ((φ t (Sx r) : LeftEnergyState μ c) : Phase) 0 ^ 2 +
          ((φ t (Sx r) : LeftEnergyState μ c) : Phase) 1 ^ 2 := by
        have : ((φ t (Sx r) : LeftEnergyState μ c) : Phase) 0 ≠ 0 := by
          rintro h0; rw [h0] at hy'; simp at hy'
        positivity
      refine ⟨hy, ?_, ?_⟩
      · exact hfv
      · rw [XRd_eq _ hP.ne']; positivity
    refine ⟨?_, ?_, ?_⟩
    · have := limit_nonpos φ Sx b hSxc (fun s => relativePosition μ s 1) (cont_relPos1 μ) t
        (key.mono fun r h => h.1.le)
      rw [hSxb, ← hγd] at this; exact this
    · have := limit_nonpos φ Sx b hSxc (fun s => -Lpoly μ s) (cont_Lpoly μ).neg t
        (key.mono fun r h => by show -Lpoly μ _ ≤ 0; linarith [h.2.1])
      rw [hSxb, ← hγd] at this; linarith
    · have := limit_nonpos φ Sx b hSxc (fun s => -XRd s) cont_XRd.neg t
        (key.mono fun r h => by show -XRd _ ≤ 0; linarith [h.2.2])
      rw [hSxb, ← hγd] at this; linarith
  -- first exit from `{x₁ < 0, x₂ < 0, v₁ > 0}`
  have hVx0 : Vx (γ 0) = 0 := by rw [hγ0]; unfold Vx; rw [hb0, hb3]; ring
  obtain ⟨ε, hε, hloc⟩ := far_start_open μ c hμ0 hμ1 hc φ hφ xb hb0 (by rw [hb1]; exact hb) hb3 hv
  set A := {s : ℝ | 0 < s ∧ ∀ t ∈ Ioo 0 s, X t < 0 ∧ Y t < 0 ∧ 0 < Vx (γ t)} with hA
  have hεA : ε ∈ A := ⟨hε, fun t ht => by
    have := hloc t ht; simp only [hX, hY, hγd]; exact this⟩
  have hPof : ∀ t, Y t < 0 → 0 < zNormSq (γ t) := by
    intro t hy; simp only [hY] at hy; rw [(relPos_eq μ _).2] at hy
    have : γ t 0 ≠ 0 := by rintro h0; rw [h0] at hy; simp at hy
    unfold zNormSq; positivity
  have hPofX : ∀ t, X t < 0 → 0 < zNormSq (γ t) := by
    intro t hx; simp only [hX] at hx; rw [(relPos_eq μ _).1] at hx
    unfold zNormSq; nlinarith [sq_nonneg (γ t 0)]
  have hbdd : BddAbove A := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    have hall : ∀ t > 0, X t < 0 ∧ Y t < 0 ∧ 0 < Vx (γ t) := by
      intro t ht
      obtain ⟨s, hs, hts⟩ := hnb t
      exact hs.2 t ⟨ht, hts⟩
    apply far_no_infinite_stay2 μ c hμ0 hμ1 hc φ hφ xb
    intro t ht
    have hneg : ∀ u ∈ Icc 0 (t + 1), X u < 0 := by
      intro u hu
      rcases eq_or_lt_of_le hu.1 with h | h
      · rw [← h]; exact hX0
      · exact (hall u h).1
    have hL := (hlimit (t + 1) (by linarith) hneg t ⟨ht, by linarith⟩).2.1
    obtain ⟨h1, h2, h3⟩ := hall t ht
    refine ⟨by simp only [hX, hγd] at h1; exact h1, by simp only [hY, hγd] at h2; exact h2,
      by rw [← hγd]; exact h3, by rw [← hγd]; exact hL⟩
  set S := sSup A with hS
  have hSε : ε ≤ S := le_csSup hbdd hεA
  have hS0 : 0 < S := lt_of_lt_of_le hε hSε
  have hopen : ∀ t ∈ Ioo 0 S, X t < 0 ∧ Y t < 0 ∧ 0 < Vx (γ t) := by
    intro t ht
    obtain ⟨s, hs, hts⟩ := (lt_csSup_iff hbdd ⟨ε, hεA⟩).1 ht.2
    exact hs.2 t ⟨ht.1, hts⟩
  have hnegS : ∀ T' ∈ Ioo 0 S, ∀ t ∈ Icc 0 T', X t < 0 := by
    intro T' hT' t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; exact hX0
    · exact (hopen t ⟨h, lt_of_le_of_lt ht.2 hT'.2⟩).1
  have hGin : ∀ t ∈ Ioo 0 S, 0 ≤ Lpoly μ (γ t) := by
    intro t ht
    exact (hlimit ((t + S) / 2) (by linarith [ht.1]) (hnegS _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      t ⟨ht.1, by linarith [ht.2]⟩).2.1
  have hGc : Continuous fun t => Lpoly μ (γ t) := (cont_Lpoly μ).comp hγc
  have hGS : 0 ≤ Lpoly μ (γ S) :=
    ge_of_tendsto (hGc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio S)))
      (by filter_upwards [Ioo_mem_nhdsLT hS0] with t ht; exact hGin t ht)
  have hXS : X S ≤ 0 :=
    le_of_tendsto (hXc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio S)))
      (by filter_upwards [Ioo_mem_nhdsLT hS0] with t ht; exact (hopen t ht).1.le)
  have hYS : Y S ≤ 0 :=
    le_of_tendsto (hYc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio S)))
      (by filter_upwards [Ioo_mem_nhdsLT hS0] with t ht; exact (hopen t ht).2.1.le)
  have hVSnn : ∀ t, 0 < t → 0 < zNormSq (γ t) → (∀ u ∈ Ioo 0 t, 0 < Vx (γ u)) → 0 ≤ Vx (γ t) := by
    intro t ht hPt hpos
    have hP' := hPt; unfold zNormSq at hP'
    have hVxc : ContinuousAt (fun u => Vx (γ u)) t := (cont_Vx _ hP'.ne').comp hγc.continuousAt
    exact ge_of_tendsto (hVxc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio t)))
      (by filter_upwards [Ioo_mem_nhdsLT ht] with u hu; exact (hpos u hu).le)
  -- the derivative facts used in the contact case
  have hYd : ∀ t, HasDerivAt Y (Yd μ (γ t)) t := by
    intro t
    have hfun : Y = fun v => relativePosition μ ((φ v xb : LeftEnergyState μ c) : Phase) 1 := by
      funext v; simp only [hY, hγd]
    rw [hfun, hγd]; exact y_hasDerivAt μ c φ hφ xb t
  have hVyd : ∀ t, 0 < zNormSq (γ t) → HasDerivAt (fun v => Vy μ (γ v))
      (4 * zNormSq (γ t) * (2 * Vx (γ t) + Omy μ (γ t))) t := by
    intro t ht
    have := vy_hasDerivAt μ c φ hφ xb t (by rw [← hγd]; exact ht)
    have hfun : (fun v => Vy μ (γ v)) = fun v => Vy μ ((φ v xb : LeftEnergyState μ c) : Phase) := by
      funext v; rw [hγd]
    rw [hfun, hγd]; exact this
  rcases lt_or_eq_of_le hXS with hXSneg | hXS0
  · -- exit strictly left of the vertical line: impossible
    exfalso
    have hPS := hPofX S hXSneg
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1
      (hXc.continuousAt.eventually (Iio_mem_nhds hXSneg))
    set T' := S + η / 2 with hT'
    have hnegT : ∀ t ∈ Icc 0 T', X t < 0 := by
      intro t ht
      rcases lt_or_ge t S with h | h
      · rcases eq_or_lt_of_le ht.1 with h' | h'
        · rw [← h']; exact hX0
        · exact (hopen t ⟨h', h⟩).1
      · exact hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.2])
    have hlimT := hlimit T' (by linarith) hnegT
    rcases lt_or_eq_of_le hYS with hYSneg | hYS0
    · -- still inside at `S`
      have hP' := hPS; unfold zNormSq at hP'
      have hVS0 := hVSnn S hS0 hPS (fun u hu => (hopen u hu).2.2)
      rcases lt_or_eq_of_le hVS0 with hVS | hVS
      · -- `S` is not the supremum
        have hVxc : ContinuousAt (fun t => Vx (γ t)) S := (cont_Vx _ hP'.ne').comp hγc.continuousAt
        obtain ⟨η2, hη2, hball2⟩ := Metric.eventually_nhds_iff.1
          ((hXc.continuousAt.eventually (Iio_mem_nhds hXSneg)).and
            ((hYc.continuousAt.eventually (Iio_mem_nhds hYSneg)).and
              (hVxc.eventually (Ioi_mem_nhds hVS))))
        have hmemA : S + η2 / 2 ∈ A := by
          refine ⟨by linarith, fun t ht => ?_⟩
          rcases lt_or_ge t S with h | h
          · exact hopen t ⟨ht.1, h⟩
          · exact hball2 (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.2])
        have := le_csSup hbdd hmemA
        linarith
      · -- `v₁` touches `0` inside: excluded by Birkhoff's two arguments
        have hγcS : Continuous fun u => ((φ u xb : LeftEnergyState μ c) : Phase) := by
          rw [← hγ]; exact hγc
        have hPev : ∀ᶠ u in 𝓝 S, 0 < zNormSq (γ u) :=
          (cont_zNormSq.comp hγc).continuousAt.eventually (Ioi_mem_nhds hPS)
        have hmin : ∀ᶠ u in 𝓝 S, 0 ≤ Vx ((φ u xb : LeftEnergyState μ c) : Phase) := by
          filter_upwards [hPev, Ioo_mem_nhds hS0 (show S < T' by linarith)] with u hu hu'
          have hx := (hlimT u hu').2.2
          have hu2 := hu; unfold zNormSq at hu2
          rw [XRd_eq _ hu2.ne'] at hx
          rw [← hγd]
          unfold zNormSq at hu
          by_contra hneg; push Not at hneg; nlinarith
        rcases le_or_gt (Vy μ (γ S)) 0 with hVy | hVy
        · exact vx_no_touch_down μ c hμ0 hμ1 hc φ hφ xb S (by rw [← hγd]; exact hPS)
            (by rw [← hγd]; exact hXSneg.le) (by rw [← hγd]; exact hYSneg)
            (by rw [← hγd]; exact hVS.symm) (by rw [← hγd]; exact hVy) hmin
        · have hL := hGS
          rw [Lpoly_eq μ _ hP'.ne', ← hVS] at hL
          have : relativePosition μ (γ S) 0 * Vy μ (γ S) < 0 := mul_neg_of_neg_of_pos hXSneg hVy
          linarith
    · -- a contact with the axis: impossible
      have hmax : IsLocalMax Y S := by
        filter_upwards [Ioo_mem_nhds hS0 (show S < T' by linarith)] with t ht
        rw [hYS0]; exact (hlimT t ht).1
      have hYd0 := hmax.hasDerivAt_eq_zero (hYd S)
      have hP' := hPS; unfold zNormSq at hP'
      rw [Yd_eq μ _ hP'.ne'] at hYd0
      have hVy0 : Vy μ (γ S) = 0 := by
        rcases mul_eq_zero.1 hYd0 with h | h
        · linarith
        · exact h
      have hVymono : StrictMonoOn (fun v => Vy μ (γ v)) (Icc (S / 2) S) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
        · intro t ht
          have hPt : 0 < zNormSq (γ t) := by
            rcases eq_or_lt_of_le ht.2 with h | h
            · rw [h]; exact hPS
            · exact hPof t (hopen t ⟨by linarith [ht.1], h⟩).2.1
          exact (hVyd t hPt).continuousAt.continuousWithinAt
        · intro t ht
          rw [interior_Icc] at ht
          have htI : t ∈ Ioo 0 S := ⟨by linarith [ht.1], ht.2⟩
          obtain ⟨-, hy, hvx⟩ := hopen t htI
          have hPt := hPof t hy
          rw [(hVyd t hPt).deriv]
          have hy' : 4 * γ t 0 * γ t 1 < 0 := by simp only [hY] at hy; rwa [(relPos_eq μ _).2] at hy
          have := omega_y_pos μ c hμ0 hμ1 hc (γ t) (hmem t) hy'
          positivity
      have hYanti : StrictAntiOn Y (Icc (S / 2) S) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
          (fun t _ => (hYd t).continuousAt.continuousWithinAt)
        intro t ht
        rw [interior_Icc] at ht
        have htI : t ∈ Ioo 0 S := ⟨by linarith [ht.1], ht.2⟩
        have hPt := hPof t (hopen t htI).2.1
        have hPt' := hPt; unfold zNormSq at hPt'
        rw [(hYd t).deriv, Yd_eq μ _ hPt'.ne']
        have := hVymono ⟨ht.1.le, ht.2.le⟩ ⟨by linarith, le_refl _⟩ ht.2
        simp only at this; rw [hVy0] at this
        unfold zNormSq at hPt
        have : 0 < 4 * (γ t 0 ^ 2 + γ t 1 ^ 2) := by positivity
        nlinarith
      have := hYanti ⟨le_refl _, by linarith⟩ ⟨by linarith, le_refl _⟩ (by linarith : S / 2 < S)
      have := (hopen (S / 2) ⟨by linarith, by linarith⟩).2.1
      linarith
  -- exit on the vertical line
  rcases lt_or_eq_of_le hYS with hYSneg | hYS0
  · -- below the axis on the vertical line
    have hPS := hPof S hYSneg
    have hP' := hPS; unfold zNormSq at hP'
    have hVS0 := hVSnn S hS0 hPS (fun u hu => (hopen u hu).2.2)
    have hyS : ∀ t ∈ Ioo 0 S, relativePosition μ ((φ t xb : LeftEnergyState μ c) : Phase) 1 < 0 := by
      intro t ht; have := (hopen t ht).2.1; simp only [hY, hγd] at this; exact this
    have hvxS : ∀ t ∈ Ioo 0 S,
        0 < jacobiVelocity (leviCivitaToJacobi μ ((φ t xb : LeftEnergyState μ c) : Phase)) 0 := by
      intro t ht; rw [(jv_eq μ _).1, ← hγd]; exact (hopen t ht).2.2
    rcases lt_or_eq_of_le hVS0 with hVS | hVS
    · -- a far arc of length `S`
      exfalso
      apply hno
      refine ⟨S, hS0, fun u hu => ?_, ?_, ?_, fun u hu => ?_⟩
      · have := (hopen u hu).2.1; simp only [hY, hγd] at this; exact this
      · simp only [hY, hγd] at hYSneg; exact hYSneg
      · simp only [hX, hγd] at hXS0; exact hXS0
      · rw [(jv_eq μ _).1, ← hγd]
        rcases eq_or_lt_of_le hu.2 with h | h
        · rw [h]; exact hVS
        · exact (hopen u ⟨hu.1, h⟩).2.2
    -- a vertical tangency
    have hXS0' : relativePosition μ ((φ S xb : LeftEnergyState μ c) : Phase) 0 = 0 := by
      simp only [hX, hγd] at hXS0; exact hXS0
    have hYS' : relativePosition μ ((φ S xb : LeftEnergyState μ c) : Phase) 1 < 0 := by
      simp only [hY, hγd] at hYSneg; exact hYSneg
    have hjv0 : jacobiVelocity (leviCivitaToJacobi μ ((φ S xb : LeftEnergyState μ c) : Phase)) 0 = 0 := by
      rw [(jv_eq μ _).1, ← hγd]; exact hVS.symm
    refine ⟨xb, hxb, by rw [(jv_eq μ _).2]; exact hv, S, hS0, fun t ht => (hyS t ht).le, hvxS,
      fun t ht => by rw [← hγd]; exact hPof t (hopen t ht).2.1, hXS0', hYS'.le, hjv0.symm.le, ?_⟩
    intro η hη
    set h := min (η / 2) (S / 2) with hh
    have hh0 : 0 < h := lt_min (half_pos hη) (half_pos hS0)
    have hhη : h ≤ η / 2 := min_le_left _ _
    have hhS : h ≤ S / 2 := min_le_right _ _
    have hlow := hlong (S - h) (by linarith) (hnegS (S - h) ⟨by linarith, by linarith⟩)
    have hup := far_tangency_upper μ c hμ0 hμ1 hc φ hφ b hb Sx hSxc hSxb hSxr hgood S hS0
      hXS0' hYS' h hh0
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
      (show ∀ᶠ r in 𝓝 b, r < b → _ from eventually_nhdsWithin_iff.1 (hlow.and hup))
    refine ⟨δ, hδ, fun r hr x τ hx harc => ?_⟩
    have hd : dist r b < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1, hr.2]
    obtain ⟨⟨-, hl⟩, hu⟩ := hball hd hr.2
    have := hl x τ hx harc
    have := hu x τ hx harc
    rw [abs_lt]; constructor <;> linarith
  -- a collision
  have hz := z_zero_of_pos_zero _ _
    (by rw [← (relPos_eq μ _).1]; simp only [hX, hγd] at hXS0; exact hXS0)
    (by rw [← (relPos_eq μ _).2]; simp only [hY, hγd] at hYS0; exact hYS0)
  obtain ⟨hc0, hc1⟩ := hz
  have hyS : ∀ t ∈ Ioo 0 S, relativePosition μ ((φ t xb : LeftEnergyState μ c) : Phase) 1 < 0 := by
    intro t ht; have := (hopen t ht).2.1; simp only [hY, hγd] at this; exact this
  have hvxS : ∀ t ∈ Ioo 0 S,
      0 < jacobiVelocity (leviCivitaToJacobi μ ((φ t xb : LeftEnergyState μ c) : Phase)) 0 := by
    intro t ht; rw [(jv_eq μ _).1, ← hγd]; exact (hopen t ht).2.2
  obtain ⟨-, hw1⟩ := birkhoff_far_collision_strict μ c hμ0 hμ1 hc φ hφ xb S hS0 (by rw [hb1]; exact hb)
    hyS hvxS hc0 hc1
  refine ⟨xb, hxb, by rw [(jv_eq μ _).2]; exact hv, S, hS0, fun t ht => (hyS t ht).le, hvxS,
    fun t ht => by rw [← hγd]; exact hPof t (hopen t ht).2.1, ?_, ?_, ?_, ?_⟩
  · rw [(relPos_eq μ _).1, hc0, hc1]; ring
  · rw [(relPos_eq μ _).2, hc0, hc1]; norm_num
  · rw [(jv_eq μ _).1]; unfold Vx; rw [hc0, hc1]; simp
  -- convergence of the arc lengths
  intro η hη
  obtain ⟨M, hM0, hM⟩ := vf_bound μ c hμ0 hμ1 hc
  set w1 := ((φ S xb : LeftEnergyState μ c) : Phase) 3 with hw1def
  set h := min (min (η / 2) (S / 2)) (-w1 / (6 * M)) with hh
  have hh0 : 0 < h := lt_min (lt_min (half_pos hη) (half_pos hS0)) (div_pos (by linarith) (by positivity))
  have hhη : h ≤ η / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hhS : h ≤ S / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hhw : h ≤ -w1 / (6 * M) := min_le_right _ _
  have hlow := hlong (S - h) (by linarith) (hnegS (S - h) ⟨by linarith, by linarith⟩)
  have hsign : ∀ u, |u| ≤ h → |((φ (u + S) xb : LeftEnergyState μ c) : Phase) 1 - w1 * u| ≤ 3 * M * h ^ 2 := by
    intro u hu
    obtain ⟨-, -, -, -, -, e5⟩ := flow_estimates μ c hμ0 hμ1 hc φ hφ M hM (φ S xb) h u hu
    rw [hc0, hc1, ← Flow.map_add] at e5
    simp only [abs_zero, sub_zero, zero_add] at e5
    have e : (M * h + 2 * (M * h)) * h = 3 * M * h ^ 2 := by ring
    rwa [e] at e5
  have h3M : 3 * M * h ^ 2 ≤ -w1 * h / 2 := by
    have : 3 * M * h ≤ -w1 / 2 := by
      have := mul_le_mul_of_nonneg_left hhw (by positivity : (0:ℝ) ≤ 3 * M)
      rw [show 3 * M * (-w1 / (6 * M)) = -w1 / 2 by field_simp; ring] at this; exact this
    nlinarith
  have hbefore : 0 < ((φ (-h + S) xb : LeftEnergyState μ c) : Phase) 1 := by
    have := (abs_le.1 (hsign (-h) (by rw [abs_neg, abs_of_pos hh0]))).1
    nlinarith
  have hafter : ((φ (h + S) xb : LeftEnergyState μ c) : Phase) 1 < 0 := by
    have := (abs_le.1 (hsign h (by rw [abs_of_pos hh0]))).2
    nlinarith
  have hcoord : Continuous fun s : Phase => s 1 := continuous_apply 1
  have hev1 := tube_pos φ Sx b hSxc (fun s => s 1) hcoord (-h + S) (-h + S)
    (by intro t ht; rw [hSxb, show t = -h + S from le_antisymm ht.2 ht.1]; exact hbefore)
  have hev2 := tube_pos φ Sx b hSxc (fun s => -s 1) hcoord.neg (h + S) (h + S)
    (by intro t ht; rw [hSxb, show t = h + S from le_antisymm ht.2 ht.1]; linarith)
  have hup : ∀ᶠ r in 𝓝[<] b, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
      (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ → τ ≤ S + h := by
    filter_upwards [Ioo_mem_nhdsLT (half_lt_self hb), nhdsWithin_le_nhds hev1,
      nhdsWithin_le_nhds hev2] with r hr h1 h2
    intro x τ hx harc
    rw [hSxr r hr x hx] at harc
    obtain ⟨hτ, hlowr, -, -, -⟩ := harc
    by_contra hlt; push Not at hlt
    have p1 := h1 (-h + S) ⟨le_rfl, le_rfl⟩
    have p2 := h2 (h + S) ⟨le_rfl, le_rfl⟩
    have hcont : ContinuousOn (fun u => ((φ u (Sx r) : LeftEnergyState μ c) : Phase) 1)
        (Icc (-h + S) (h + S)) :=
      fun u _ => ((flow_coords' μ c φ hφ (Sx r) u).2.1).continuousAt.continuousWithinAt
    obtain ⟨u, hu, hu0⟩ := intermediate_value_Icc' (by linarith) hcont ⟨by linarith, p1.le⟩
    simp only at hu0
    have := hlowr u ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rw [(relPos_eq μ _).2, hu0] at this; simp at this
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    (show ∀ᶠ r in 𝓝 b, r < b → _ from eventually_nhdsWithin_iff.1 (hlow.and hup))
  refine ⟨δ, hδ, fun r hr x τ hx harc => ?_⟩
  have hd : dist r b < δ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1, hr.2]
  obtain ⟨⟨-, hl⟩, hu⟩ := hball hd hr.2
  have := hl x τ hx harc
  have := hu x τ hx harc
  rw [abs_lt]; constructor <;> linarith

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (b : ℝ) (hb : 0 < b)
    (hgood : ∀ r ∈ Set.Ioo 0 b, ∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c r ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ)
    (hbad : ¬ (∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c b ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ)) :
    ∃ xb : LeftEnergyState μ c, (xb : Phase) = farShootingStart μ c b ∧
      jacobiVelocity (leviCivitaToJacobi μ (xb : Phase)) 1 < 0 ∧ ∃ T : ℝ, 0 < T ∧
      (∀ t ∈ Set.Ioo 0 T, relativePosition μ ((φ t xb : LeftEnergyState μ c) : Phase) 1 ≤ 0) ∧
      (∀ t ∈ Set.Ioo 0 T, 0 < jacobiVelocity (leviCivitaToJacobi μ ((φ t xb : LeftEnergyState μ c) : Phase)) 0) ∧
      (∀ t ∈ Set.Ioo 0 T, 0 < zNormSq ((φ t xb : LeftEnergyState μ c) : Phase)) ∧
      relativePosition μ ((φ T xb : LeftEnergyState μ c) : Phase) 0 = 0 ∧ relativePosition μ ((φ T xb : LeftEnergyState μ c) : Phase) 1 ≤ 0 ∧
      0 ≤ jacobiVelocity (leviCivitaToJacobi μ ((φ T xb : LeftEnergyState μ c) : Phase)) 0 ∧
      ∀ η > 0, ∃ δ > 0, ∀ r ∈ Set.Ioo (b - δ) b, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
        (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ → |τ - T| < η
 :=
  far_arc_limit_rest μ c hμ0 hμ1 hc φ hφ b hb hgood hbad
