-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_uniform_prefix_preruin_compact_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:54:26.861216+00:00
-- url     : https://prove2.me/submissions/7ff37503-57a2-404e-8045-4777b2c529ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The physical pre-ruin source and reserve remain in the source-exact compact strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (κ : Ω → ℝ≥0) (B : ℝ)
    (hXprefix : ∀ ω (t : ℝ≥0), t ≤ κ ω → X.X t ω ≤ B) :
    ∀ ω (t : ℝ≥0), t ≤ κ ω →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      X.X t ω ∈ Icc (-x) B ∧
      riskProcess X x D t ω ∈ Icc 0 (x + B) := by
  intro ω t ht hpre
  have hr : 0 ≤ riskProcess X x D t ω :=
    riskProcess_nonnegative_strictly_before_ruin X x D ω t hpre
  have hd : 0 ≤ D t ω := dividendStrategy_path_nonneg D hD ω t
  have hx : X.X t ω ≤ B := hXprefix ω t ht
  constructor
  · change -x ≤ X.X t ω ∧ X.X t ω ≤ B
    constructor
    · dsimp [riskProcess] at hr
      linarith
    · exact hx
  · change 0 ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + B
    constructor
    · exact hr
    · unfold riskProcess
      linarith
