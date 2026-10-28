-- Prove2me | solution 1 for AvramDividend.Classical.surviving_higher_record_has_finite_clock_pair_and_delay
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:05:28.410367+00:00
-- url     : https://prove2.me/submissions/9349bd7c-8acd-44ab-9328-f011b366a601

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε : ℝ) (hε : 0 ≤ ε)
    (hSurvive : twoSidedExitUpTime X (b + ε) ω <
      barrierRuinTime X a ω) :
    ∃ u v δ : ℝ≥0,
      (u : ℝ≥0∞) = twoSidedExitUpTime X b ω ∧
      (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω ∧
      u + δ = v := by 
  have hle := twoSidedExitUpTime_mono_threshold X b (b + ε) (by linarith) ω
  have hvt : twoSidedExitUpTime X (b + ε) ω ≠ ⊤ := ne_top_of_lt hSurvive
  have hut : twoSidedExitUpTime X b ω ≠ ⊤ := ne_top_of_le_ne_top hvt hle
  refine ⟨(twoSidedExitUpTime X b ω).toNNReal, (twoSidedExitUpTime X (b + ε) ω).toNNReal,
    (twoSidedExitUpTime X (b + ε) ω).toNNReal - (twoSidedExitUpTime X b ω).toNNReal,
    ENNReal.coe_toNNReal hut, ENNReal.coe_toNNReal hvt, add_tsub_cancel_of_le ?_⟩
  exact ENNReal.toNNReal_mono hvt hle
