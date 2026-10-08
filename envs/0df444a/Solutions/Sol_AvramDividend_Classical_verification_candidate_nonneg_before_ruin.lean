-- Prove2me | solution 1 for AvramDividend.Classical.verification_candidate_nonneg_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T11:24:16.432991+00:00
-- url     : https://prove2.me/submissions/954f0535-4666-4913-9cbb-49676f64960e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_hjb_candidate_ge_capital
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (ht0 : 0 < t)
    (htru : (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ w (riskProcess X x D t ω) := by
  have hr0 : 0 ≤ riskProcess X x D t ω :=
    riskProcess_nonneg_before_ruin X x D ω t htru
  have hcap : ENNReal.ofReal (riskProcess X x D t ω) ≤ C :=
    hD.2 ω t ht0
  have hle := hjb_candidate_ge_capital
    X q w C hw_cont hw0 hw_smooth hw_hjb
    (riskProcess X x D t ω) hr0 hcap
  linarith
