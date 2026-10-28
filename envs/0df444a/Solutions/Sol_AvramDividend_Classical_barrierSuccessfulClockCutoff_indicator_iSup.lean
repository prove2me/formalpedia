-- Prove2me | solution 1 for AvramDividend.Classical.barrierSuccessfulClockCutoff_indicator_iSup
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:14:12.371094+00:00
-- url     : https://prove2.me/submissions/0d1d3448-7f9b-4750-a108-a57ccc72ed29

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} (τ σ : Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞) :
    (fun ω => if τ ω < σ ω then g ω else 0) =
      ⨆ n : ℕ, fun ω =>
        if τ ω < σ ω ∧ τ ω ≤ ((n : ℝ≥0) : ℝ≥0∞) then g ω else 0 := by
  funext ω
  rw [iSup_apply]
  by_cases h : τ ω < σ ω
  · rw [if_pos h]
    apply le_antisymm
    · have hτ : τ ω ≠ ⊤ := ne_top_of_lt h
      obtain ⟨n, hn⟩ := exists_nat_gt (τ ω).toReal
      have hle : τ ω ≤ ((n : ℝ≥0) : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_toReal hτ]
        simpa using ENNReal.ofReal_le_ofReal hn.le
      refine le_iSup_of_le n ?_
      rw [if_pos ⟨h, hle⟩]
    · exact iSup_le fun n => by split_ifs <;> simp
  · rw [if_neg h]
    symm
    exact le_antisymm (iSup_le fun n => by rw [if_neg (fun h' => h h'.1)]) bot_le
