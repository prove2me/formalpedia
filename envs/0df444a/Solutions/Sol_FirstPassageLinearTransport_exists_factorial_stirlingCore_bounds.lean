-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_factorial_stirlingCore_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:00.664111+00:00
-- url     : https://prove2.me/submissions/c3e4c540-6824-4c8c-a23a-2e5dcab6f3aa

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_stirlingSeq_eq_factorial_div_core
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ n : ℕ, 0 < n →
        a * stirlingCore n ≤ (Nat.factorial n : ℝ) ∧
          (Nat.factorial n : ℝ) ≤ b * stirlingCore n := by
  obtain ⟨a, ha, hlow⟩ := Stirling.stirlingSeq'_bounded_by_pos_constant
  refine ⟨a, Stirling.stirlingSeq 1, ha, Stirling.stirlingSeq'_pos 0, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hcore : 0 < stirlingCore (m + 1) := by
    unfold stirlingCore
    positivity
  have hlo : a ≤ (Nat.factorial (m + 1) : ℝ) / stirlingCore (m + 1) := by
    simpa [stirlingSeq_eq_factorial_div_core] using hlow m
  have hup : (Nat.factorial (m + 1) : ℝ) / stirlingCore (m + 1) ≤ Stirling.stirlingSeq 1 := by
    simpa [stirlingSeq_eq_factorial_div_core] using
      Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  constructor
  · exact (le_div_iff₀ hcore).mp hlo
  · exact (div_le_iff₀ hcore).mp hup
end FirstPassageLinearTransport
