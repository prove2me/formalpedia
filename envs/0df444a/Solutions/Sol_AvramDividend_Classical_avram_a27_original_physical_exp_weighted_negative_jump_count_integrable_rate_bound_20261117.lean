-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_exp_weighted_negative_jump_count_integrable_rate_bound_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:36:45.691729+00:00
-- url     : https://prove2.me/submissions/3f91ddf4-9bbd-4d51-bc48-dc680cd1c92d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_laplace_factor_le_one_20261117
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_negative_Borel_marked_interval_real_count_integrable_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original physical negative-jump exponential weighted count is integrable and dominated by its Lévy intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal) :
    Integrable (fun ω => (K ω : ℝ) * Real.exp (θ * J ω)) P ∧
      0 ≤ (∫ ω, (K ω : ℝ) * Real.exp (θ * J ω) ∂P) ∧
      (∫ ω, (K ω : ℝ) * Real.exp (θ * J ω) ∂P) ≤
        (((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ Iio (0 : ℝ))
  have hEq : (fun ω => (K ω : ℝ)) =ᵐ[P]
      (fun ω => (N ω).toReal) := hCount
  have hSrc :=
    avram_b24_original_negative_Borel_marked_interval_real_count_integrable_mean
      X hFinite 0 t bot_le (Iio (0 : ℝ))
      measurableSet_Iio Subset.rfl
  have hIntCount : Integrable (fun ω => (K ω : ℝ)) P := by
    exact hSrc.1.congr hEq.symm
  have hBound :=
    avram_a27_original_physical_negative_jump_laplace_factor_le_one_20261117
      X hFinite t θ hθ J hJEq
  have hMeas : Measurable (fun ω => (K ω : ℝ) * Real.exp (θ * J ω)) :=
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hK).mul
      (Real.measurable_exp.comp (measurable_const.mul hJMeas))
  have hInt : Integrable
      (fun ω => (K ω : ℝ) * Real.exp (θ * J ω)) P :=
    hIntCount.mono hMeas.aestronglyMeasurable (by
      filter_upwards [hBound] with ω hω
      have hnn : 0 ≤ (K ω : ℝ) := Nat.cast_nonneg _
      have hPos : 0 ≤ (K ω : ℝ) * Real.exp (θ * J ω) :=
        mul_nonneg hnn (le_of_lt hω.1)
      rw [Real.norm_eq_abs, abs_of_nonneg hPos,
        Real.norm_eq_abs, abs_of_nonneg hnn]
      calc
        (K ω : ℝ) * Real.exp (θ * J ω) ≤
          (K ω : ℝ) * 1 := mul_le_mul_of_nonneg_left hω.2 hnn
        _ = (K ω : ℝ) := mul_one _)
  have hCountMean :
      (∫ ω, (K ω : ℝ) ∂P) =
        (((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) := by
    calc
      (∫ ω, (K ω : ℝ) ∂P) =
          (∫ ω, (N ω).toReal ∂P) := integral_congr_ae hEq
      _ = _ := by simpa [N] using hSrc.2
  refine ⟨hInt, ?_, ?_⟩
  · exact integral_nonneg (fun ω =>
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt (Real.exp_pos _)))
  · have hUpper := integral_mono_ae hInt hIntCount (by
      filter_upwards [hBound] with ω hω
      exact (mul_le_mul_of_nonneg_left hω.2
        (Nat.cast_nonneg (K ω))).trans_eq (mul_one _))
    exact hUpper.trans_eq hCountMean
