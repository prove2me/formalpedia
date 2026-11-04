-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_finitecap_continuous_payoff_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:24:18.111073+00:00
-- url     : https://prove2.me/submissions/f07a95fc-f568-4125-9d1b-b4d5d4405b3e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Source nonnegative half-line continuity supplies an actual uniform terminal-payoff bound on finite cap states. -/
theorem solution
    (w : ℝ → ℝ) (hwcont : ContinuousOn w (Ici 0))
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y : ℝ, 0 ≤ y →
        ENNReal.ofReal y ≤ ENNReal.ofReal c → |w y| ≤ B := by
  have hs : (Icc (0 : ℝ) c).Nonempty := nonempty_Icc.mpr hc
  have hwIcc : ContinuousOn w (Icc (0 : ℝ) c) :=
    hwcont.mono (by intro y hy; exact hy.1)
  obtain ⟨z, hz, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn hs hwIcc.abs
  refine ⟨|w z|, abs_nonneg _, ?_⟩
  intro y hy hOf
  have hyc : y ≤ c := by
    have h := ENNReal.toReal_le_of_le_ofReal hc hOf
    simpa only [ENNReal.toReal_ofReal hy] using h
  exact hmax ⟨hy, hyc⟩