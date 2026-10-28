-- Prove2me | solution 1 for AvramDividend.Classical.monotone_localised_reward_lintegral_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:40:03.417003+00:00
-- url     : https://prove2.me/submissions/cbb363b7-6b51-4651-adcb-b4f479e1fcc1

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
