-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_marked_bounded_random_weight_short_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:52:07.252638+00:00
-- url     : https://prove2.me/submissions/de30e409-b28e-45f0-a68e-8dfafb96928c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_marked_rectangle_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal

/-- For the actual intrinsic original Lévy count, bounded random
coefficients have short-strip weighted expectation bounded by K times the
unconditional physical source jump intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s r : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (A : Set Ω) (H : Ω → ℝ≥0∞) (K : ℝ≥0∞)
    (hBound : ∀ ω, H ω ≤ K)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s r ×ˢ B) ∂P) =
       ((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫⁻ ω in A, H ω * ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s r ×ˢ B) ∂P) ≤
      K * (((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  let J : Ω → ℝ≥0∞ := fun ω =>
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
      (Ioc s r ×ˢ B)
  have hMeas : Measurable J := by
    simpa only [J] using
      (avram_p2_d_future_intrinsic_marked_rectangle_measurable X s r B hB)
  change (∫⁻ ω in A, H ω * J ω ∂P) ≤
    K * (((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
  calc
    (∫⁻ ω in A, H ω * J ω ∂P) ≤
        (∫⁻ ω in A, K * J ω ∂P) := by
      apply lintegral_mono
      intro ω
      exact mul_le_mul_of_nonneg_right (hBound ω) (zero_le : (0 : ℝ≥0∞) ≤ J ω)
    _ = K * (∫⁻ ω in A, J ω ∂P) := lintegral_const_mul K hMeas
    _ ≤ K * (∫⁻ ω, J ω ∂P) := by
      exact mul_le_mul_of_nonneg_left (by simpa using
        (lintegral_mono_set (Set.subset_univ A) :
          (∫⁻ ω in A, J ω ∂P) ≤
            (∫⁻ ω in Set.univ, J ω ∂P))) (zero_le : (0 : ℝ≥0∞) ≤ K)
    _ = K * (((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
      rw [hRate]
