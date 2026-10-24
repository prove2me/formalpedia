-- Prove2me | solution 1 for AvramDividend.Classical.capped_discounted_random_horizon_terminal_test_expected_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:12:07.405418+00:00
-- url     : https://prove2.me/submissions/9f038562-ceaa-401f-84ea-a87822b7d790

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_random_horizon_surviving_test_expected_bounded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Positive discounting preserves the integrable finite-cap terminal bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B) (q : ℝ) (hq : 0 ≤ q)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (τ : Ω → ℝ≥0) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∫⁻ ω, if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
        ENNReal.ofReal (|Real.exp (-(q * (τ ω : ℝ))) *
          w (riskProcess X x D (τ ω) ω)|) else 0 ∂P) ≤
      ENNReal.ofReal M := by
  obtain ⟨M, hM0, hBound⟩ :=
    capped_random_horizon_surviving_test_expected_bounded
      X w hw B hB x hx hxc D hD τ
  refine ⟨M, hM0, ?_⟩
  calc
    (∫⁻ ω, if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
        ENNReal.ofReal (|Real.exp (-(q * (τ ω : ℝ))) *
          w (riskProcess X x D (τ ω) ω)|) else 0 ∂P) ≤
      (∫⁻ ω, if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
        ENNReal.ofReal (|w (riskProcess X x D (τ ω) ω)|) else 0 ∂P) := by
      apply lintegral_mono
      intro ω
      change (if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
        ENNReal.ofReal (|Real.exp (-(q * (τ ω : ℝ))) *
          w (riskProcess X x D (τ ω) ω)|) else 0) ≤
        (if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
          ENNReal.ofReal (|w (riskProcess X x D (τ ω) ω)|) else 0)
      split_ifs with hSurvive
      · have hτ : 0 ≤ (τ ω : ℝ) := (τ ω).property
        have hqτ : 0 ≤ q * (τ ω : ℝ) := mul_nonneg hq hτ
        have hDiscount : Real.exp (-(q * (τ ω : ℝ))) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqτ)
        apply ENNReal.ofReal_le_ofReal
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        calc
          Real.exp (-(q * (τ ω : ℝ))) *
              |w (riskProcess X x D (τ ω) ω)| ≤
              1 * |w (riskProcess X x D (τ ω) ω)| :=
            mul_le_mul_of_nonneg_right hDiscount (abs_nonneg _)
          _ = |w (riskProcess X x D (τ ω) ω)| := one_mul _
      · exact le_refl _
    _ ≤ ENNReal.ofReal M := hBound
