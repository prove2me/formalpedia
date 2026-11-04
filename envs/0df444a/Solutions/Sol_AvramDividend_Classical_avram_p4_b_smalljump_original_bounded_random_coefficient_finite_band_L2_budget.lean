-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_bounded_random_coefficient_finite_band_L2_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:25:35.752734+00:00
-- url     : https://prove2.me/submissions/226ab4d4-1b96-4e91-a179-0b6c7e8d7af1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A uniformly bounded random coefficient on a genuine original marked
count has its quadratic physical-P budget bounded by the source rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (J H : Ω → ℝ)
    (hSource : ∀ ω, J ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)
    (r : ℝ) (hRate : r =
      ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (C : ℝ) (hC : 0 ≤ C) (hBound : ∀ ω, |H ω| ≤ C)
    (hBaseInt : Integrable (fun ω => (J ω - r) ^ 2) P)
    (hWeightedInt : Integrable
      (fun ω => (H ω * (J ω - r)) ^ 2) P)
    (hVar : (∫ ω, (J ω - r) ^ 2 ∂P) = r) :
    (∫ ω, (H ω * (J ω - r)) ^ 2 ∂P) ≤ C ^ 2 * r := by
  have hPoint (ω : Ω) :
      (H ω * (J ω - r)) ^ 2 ≤ C ^ 2 * (J ω - r) ^ 2 := by
    have hLow : -C ≤ H ω := (abs_le.mp (hBound ω)).1
    have hHigh : H ω ≤ C := (abs_le.mp (hBound ω)).2
    have hSq : H ω ^ 2 ≤ C ^ 2 := by
      have hNonneg : 0 ≤ (C - H ω) * (C + H ω) :=
        mul_nonneg (sub_nonneg.mpr hHigh) (by linarith)
      nlinarith
    have hVarSq : 0 ≤ (J ω - r) ^ 2 := sq_nonneg _
    have hProd : 0 ≤ (C ^ 2 - H ω ^ 2) * (J ω - r) ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hSq) hVarSq
    nlinarith
  calc
    _ ≤ (∫ ω, C ^ 2 * (J ω - r) ^ 2 ∂P) := by
      apply integral_mono_ae hWeightedInt (hBaseInt.const_mul _)
      exact Filter.Eventually.of_forall hPoint
    _ = C ^ 2 * r := by
      rw [integral_const_mul, hVar]
