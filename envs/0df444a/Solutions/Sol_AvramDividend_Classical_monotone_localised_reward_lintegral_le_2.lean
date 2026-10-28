-- Prove2me | solution 2 for AvramDividend.Classical.monotone_localised_reward_lintegral_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:40:14.799748+00:00
-- url     : https://prove2.me/submissions/607a9d34-6a60-42c4-acc7-541717280685

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory
open AvramDividend.Classical
open scoped ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (reward : ℕ → Ω → ℝ≥0∞)
    (hreward : ∀ n, Measurable (reward n))
    (hmono : Monotone reward)
    (bound : ℝ≥0∞)
    (hbound : ∀ n, (∫⁻ ω, reward n ω ∂P) ≤ bound) :
    (∫⁻ ω, ⨆ n, reward n ω ∂P) ≤ bound := by 
  rw [lintegral_iSup hreward hmono]
  exact iSup_le hbound
