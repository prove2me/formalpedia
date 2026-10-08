-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_stochastic_test_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:28:51.885001+00:00
-- url     : https://prove2.me/submissions/c011dfd9-5894-448a-b0b0-441ec45df1b8

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Theorems.Thm_AvramDividend_Classical_local_verification_w_nonneg_below_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by
  intro ω t ht hruin
  have hnonneg : 0 ≤ riskProcess X x D t ω :=
    riskProcess_nonneg_before_ruin X x D ω t hruin
  have hcap : ENNReal.ofReal (riskProcess X x D t ω) ≤ C :=
    admissibleLe_riskProcess_le_cap_all_times X x C D hD hxC ω t
  exact local_verification_w_nonneg_below_cap
    X q w C hw_cont hw0 hw_smooth hw_hjb
    (riskProcess X x D t ω) hnonneg hcap
