-- Prove2me | solution 1 for AvramDividend.Classical.avram_reuse8_barrierValue_original_preruin_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:25:39.425391+00:00
-- url     : https://prove2.me/submissions/bfb7cd47-9d99-440b-8fea-d77ceaded6ee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 ≤ a)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ barrierValue W a (riskProcess X x D t ω) := by
  intro ω t _ ht
  exact barrierValue_nonnegative_for_nonnegative_capital
    X hX q hq W hW a (riskProcess X x D t ω) ha
    (riskProcess_nonnegative_strictly_before_ruin X x D ω t ht)
