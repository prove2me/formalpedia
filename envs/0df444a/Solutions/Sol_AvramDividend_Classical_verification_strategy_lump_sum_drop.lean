-- Prove2me | solution 1 for AvramDividend.Classical.verification_strategy_lump_sum_drop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T18:50:16.996639+00:00
-- url     : https://prove2.me/submissions/8a33c8b0-faa3-4f09-af27-2632db8cc963

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_verification_candidate_capped_lump_sum_drop
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_admissibleLe_reserve_cap_at_jump_time

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
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_diff : DifferentiableOn ℝ w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D t ω - D t ω ≤
      w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) := by
  have hδ : 0 ≤ rightLimit D t ω - D t ω :=
    sub_nonneg.mpr
      (dividendStrategy_le_rightLimit D hD.1.1 ω t)
  have hadm :
      rightLimit D t ω - D t ω ≤ riskProcess X x D t ω :=
    hD.1.2 ω t ht
  have hpost :
      0 ≤ riskProcess X x D t ω - (rightLimit D t ω - D t ω) :=
    sub_nonneg.mpr hadm
  have hcap : ENNReal.ofReal (riskProcess X x D t ω) ≤ C :=
    admissibleLe_reserve_cap_at_jump_time X x C hxc D hD ω t ht
  exact verification_candidate_capped_lump_sum_drop
    w C hw_cont hw_diff hw_grad
    (riskProcess X x D t ω) (rightLimit D t ω - D t ω)
    hδ hpost hcap
