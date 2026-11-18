-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_negative_mark_count_pgf_unit_bound_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:32:43.013205+00:00
-- url     : https://prove2.me/submissions/fc50d88c-e9d6-4387-9fd7-9a2e0ba1db1d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_laplace_factor_le_one_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original negative-jump marked-count PGF takes values in the unit interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ (∫ ω, z ^ K ω * Real.exp (θ * J ω) ∂P) ∧
      (∫ ω, z ^ K ω * Real.exp (θ * J ω) ∂P) ≤ 1 := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hInt :=
    avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
      X hFinite t θ hθ J hJMeas hJEq K hK z hz hz1
  have hBound :=
    avram_a27_original_physical_negative_jump_laplace_factor_le_one_20261117
      X hFinite t θ hθ J hJEq
  have hPow : ∀ n : ℕ, z ^ n ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n hn =>
      rw [pow_succ]
      calc
        z ^ n * z ≤ (1 : ℝ) * z :=
          mul_le_mul_of_nonneg_right hn hz
        _ = z := one_mul z
        _ ≤ 1 := hz1
  have hUp :
      (∫ ω, z ^ K ω * Real.exp (θ * J ω) ∂P) ≤
        (∫ _ : Ω, (1 : ℝ) ∂P) := by
    apply integral_mono_ae hInt (integrable_const (1 : ℝ))
    filter_upwards [hBound] with ω hω
    calc
      z ^ K ω * Real.exp (θ * J ω) ≤
          (1 : ℝ) * Real.exp (θ * J ω) :=
            mul_le_mul_of_nonneg_right (hPow (K ω)) (le_of_lt hω.1)
      _ = Real.exp (θ * J ω) := one_mul _
      _ ≤ 1 := hω.2
  refine ⟨integral_nonneg (fun ω =>
    mul_nonneg (pow_nonneg hz _) (le_of_lt (Real.exp_pos _))), ?_⟩
  simpa using hUp
