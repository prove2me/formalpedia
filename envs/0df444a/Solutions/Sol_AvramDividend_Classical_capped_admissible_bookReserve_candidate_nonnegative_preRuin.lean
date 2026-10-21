-- Prove2me | solution 1 for AvramDividend.Classical.capped_admissible_bookReserve_candidate_nonnegative_preRuin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:42:40.935046+00:00
-- url     : https://prove2.me/submissions/6991ff5b-8c78-4413-afd3-785771fb6e15

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_candidate_lower_bound_on_cap

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
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by
  intro ω t ht hruin
  have hs : IsDividendStrategy 𝓕 D := hD.1.1
  have hUplus : 0 ≤ x + X.X t ω - rightLimit D t ω :=
    postPaymentReserve_nonnegative_strictly_before_ruin
      X x D hs ω t hruin
  have hdrop : x + X.X t ω - rightLimit D t ω ≤
      riskProcess X x D t ω :=
    (postPaymentReserve_rightJump_decomposition X x D hs ω t).2.2
  have hU : 0 ≤ riskProcess X x D t ω :=
    hUplus.trans hdrop
  have hcap : ENNReal.ofReal (riskProcess X x D t ω) ≤ C :=
    hD.2 ω t ht
  exact (local_verification_hjb_candidate_lower_bound_on_cap
    X q w C hw_cont hw0 hw_smooth hw_hjb
    (riskProcess X x D t ω) hU hcap).2
