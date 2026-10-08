-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_capped_admissible_jump_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:28:54.252988+00:00
-- url     : https://prove2.me/submissions/f2bad4c0-f23c-4d37-8fec-33614513c43c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_controls_dividend_jump_le_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D t ω - D t ω ≤
      w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) := by
  have huCap : ENNReal.ofReal (riskProcess X x D t ω) ≤ C :=
    admissibleLe_riskProcess_le_cap_all_times X x C D hD hxC ω t
  have hd : 0 ≤ rightLimit D t ω - D t ω :=
    sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD.1.1 ω t)
  have hdCap : rightLimit D t ω - D t ω ≤ riskProcess X x D t ω :=
    hD.1.2 ω t ht
  exact local_verification_hjb_controls_dividend_jump_le_cap X q w C
    hw_cont hw_smooth hw_hjb
    (riskProcess X x D t ω) (rightLimit D t ω - D t ω)
    hd hdCap huCap
