-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_BV_uniform_pathwise_terminal_all_finite_clocks_ae_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:10:16.430791+00:00
-- url     : https://prove2.me/submissions/30665c79-e7ef-47ad-98b0-ee67f35d6812

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_postpayment_deterministic_horizon_upper_strip
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- One path event dominates every clock through the finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ H →
        (if (t : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (t : ℝ))) *
            w (x + X.X t ω - rightLimit D t ω))
        else 0) ≤ K := by
  classical
  have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hDrift : 0 ≤ X.drift :=
    le_of_lt (bv_standing_drift_pos X hX hBV).1
  let B : ℝ := max 0 (x + (H : ℝ) * X.drift)
  have hB0 : 0 ≤ B := le_max_left _ _
  obtain ⟨M, hM0, hM⟩ :=
    continuous_test_abs_le_on_finite_cap w B hB0 hw_cont
  have hUpper : ∀ᵐ ω ∂P, ∀ (t : ℝ≥0), t ≤ H →
      x + X.X t ω - rightLimit D t ω ≤
        x + (H : ℝ) * X.drift :=
    avram_wave7_02_original_BV_postpayment_deterministic_horizon_upper_strip
      X hBV x D hStrat H hDrift
  refine ⟨M, hM0, ?_⟩
  filter_upwards [hUpper] with ω hCeil
  intro t ht
  by_cases hSurv : (t : ℝ≥0∞) < ruinTime X x D ω
  · have hY0 : 0 ≤ x + X.X t ω - rightLimit D t ω :=
      postPaymentReserve_nonnegative_strictly_before_ruin
        X x D hStrat ω t hSurv
    have hYB : x + X.X t ω - rightLimit D t ω ≤ B :=
      (hCeil t ht).trans (le_max_right _ _)
    have hWUpper : w (x + X.X t ω - rightLimit D t ω) ≤ M :=
      (abs_le.mp (hM _ hY0 hYB)).2
    have hExpPos : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
      Real.exp_nonneg _
    have hExpLE : Real.exp (-(q * (t : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      apply neg_nonpos.mpr
      exact mul_nonneg (le_of_lt hq) (NNReal.coe_nonneg _)
    have hProduct : Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω) ≤ M := by
      calc
        _ ≤ Real.exp (-(q * (t : ℝ))) * M :=
          mul_le_mul_of_nonneg_left hWUpper hExpPos
        _ ≤ 1 * M := mul_le_mul_of_nonneg_right hExpLE hM0
        _ = M := one_mul M
    have hMax : max 0 (Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω)) ≤ M :=
      max_le hM0 hProduct
    simpa only [if_pos hSurv] using hMax
  · simpa only [if_neg hSurv] using hM0
