-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_paymentTimes_after_firstUpcrossing_no_preRuin_breach
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:51:14.690703+00:00
-- url     : https://prove2.me/submissions/59f0228d-5f96-42fa-b6e1-22a814bed774

import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Until ruin the controlled surplus remains nonnegative, hence the
drawdown cannot yet have breached its barrier after first passage. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (ω : Ω) (u : ℝ≥0)
    (hdraw : ∀ t : ℝ≥0,
      riskProcess X x (barrierStrategy X x a) (u + t) ω < 0 ↔
        a < runningSup X (u + t) ω - X.X (u + t) ω) :
    {t : ℝ≥0 | u < t ∧
        (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω} =
      {t : ℝ≥0 | u < t ∧
        (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω ∧
        ¬ a < runningSup X t ω - X.X t ω} := by
  ext t
  constructor
  · intro ht
    refine ⟨ht.1, ht.2, ?_⟩
    have hle : u ≤ t := le_of_lt ht.1
    have hSafe : 0 ≤ riskProcess X x (barrierStrategy X x a) t ω :=
      riskProcess_nonneg_before_ruin X x (barrierStrategy X x a) ω t ht.2
    have hLink := hdraw (t - u)
    rw [add_tsub_cancel_of_le hle] at hLink
    intro hBreach
    exact (not_lt_of_ge hSafe) (hLink.mpr hBreach)
  · intro ht
    exact ⟨ht.1, ht.2.1⟩
