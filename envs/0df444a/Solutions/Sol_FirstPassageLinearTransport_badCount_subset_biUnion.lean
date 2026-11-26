-- Prove2me | solution 1 for FirstPassageLinearTransport.badCount_subset_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:32.36372+00:00
-- url     : https://prove2.me/submissions/b2482cdd-41ac-4572-8647-5503170cfe90

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.mem_prefixBad

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (S : Set ℕ) (X : ℕ) :
    prefixBad S X ⊆
      (Finset.range (Nat.log 2 X + 1)).biUnion (shellBad S) := by
  classical
  intro n hn
  rw [mem_prefixBad] at hn
  obtain ⟨hn1, hnX, hnS⟩ := hn
  have hn0 : n ≠ 0 := by omega
  refine Finset.mem_biUnion.2 ⟨Nat.log 2 n, ?_, ?_⟩
  · exact Finset.mem_range.2
      (Nat.lt_succ_of_le (Nat.log_mono_right hnX))
  · rw [shellBad, Finset.mem_filter, mem_dyadicShell]
    exact ⟨⟨Nat.pow_log_le_self 2 hn0,
      Nat.lt_pow_succ_log_self (by norm_num) n⟩, hnS⟩
end FirstPassageLinearTransport
