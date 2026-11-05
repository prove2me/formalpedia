-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_reward_L1_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:38:16.494797+00:00
-- url     : https://prove2.me/submissions/72bb9d4c-0d4d-49f4-bd44-c7500031ff93

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- At positive time the actual original strict Stieltjes cash and
pre-rightpayment survival value form a nonnegative integrable reward.
This retains the zero-time dividend atom and original ruin predicate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let Strict : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
    Integrable Strict P ∧ ∀ ω, 0 ≤ Strict ω := by
  intro S Strict
  constructor
  · exact avram_p3_bv_original_prebudget_L1
      X hBV x C D hD w hw_cont hw_neg q hq T hT
  · intro ω
    have hSpos : 0 < S := by exact_mod_cast hTpos
    have hCash : 0 ≤
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal := ENNReal.toReal_nonneg
    have hTerm : 0 ≤
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) := by
      split_ifs with hSurv
      · exact mul_nonneg (Real.exp_pos _).le
          (hw_nonneg ω S hSpos hSurv)
      · exact le_refl _
    exact add_nonneg hCash hTerm
