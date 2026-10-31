-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:32:58.121433+00:00
-- url     : https://prove2.me/submissions/7a2828d9-9f89-4f1b-a4b0-56972dcf5f68

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal

/-- A real-valued path on nonnegative time with finite strict-left limits
has a left-continuous left-limit modification, including at time zero. -/
theorem solution
    (f : ℝ≥0 → ℝ)
    (hleft : ∀ t : ℝ≥0, 0 < t →
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l)) :
    ∀ t : ℝ≥0, ContinuousWithinAt (Function.leftLim f) (Iic t) t := by
  intro t
  apply continuousWithinAt_leftLim_Iic
  by_cases ht : t = 0
  · subst t
    have hbot : (𝓝[<] (0 : ℝ≥0)) = ⊥ := by simp
    rw [hbot]
    exact tendsto_bot
  · have htpos : 0 < t := pos_iff_ne_zero.mpr ht
    letI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
    obtain ⟨l, hl⟩ := hleft t htpos
    have heq : Function.leftLim f t = l := by
      exact leftLim_eq_of_tendsto hl
    rw [heq]
    exact hl
