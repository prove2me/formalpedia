-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_driftpos_eventual_psi_above_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T12:42:10.637884+00:00
-- url     : https://prove2.me/submissions/f064392a-43f8-4cf7-bc09-2e8f5ef3d044

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_scale_ratio_gap

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hdrift : 0 < X.drift)
    (hBV : X.BoundedVariation) :
    ∃ β₀ : ℝ, 0 ≤ β₀ ∧ ∀ θ : ℝ, β₀ ≤ θ → q < X.ψ θ := by
  have h := (p2m81_bv_scale_ratio_gap X hBV q hdrift).1
  obtain ⟨b, hb⟩ := eventually_atTop.mp h
  refine ⟨max 0 b, le_max_left _ _, ?_⟩
  intro θ hθ
  exact (hb θ ((le_max_right _ _).trans hθ)).2
