-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_fixedSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:58.850641+00:00
-- url     : https://prove2.me/submissions/8446dce8-510a-43b0-b040-0672c7103890

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSet_zero
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet_succ
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N s : ℕ) (hN : 0 < N) (hs : 0 < s) :
    (fixedSet N s).card = (N - 1).choose (s - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  induction k generalizing s with
  | zero =>
      have hlength : ∀ c : Composition 1, c.length = 1 := by
        intro c
        have hpos := c.length_pos_of_pos (by norm_num)
        have hle := c.length_le
        omega
      by_cases hs1 : s = 1
      · subst s
        simp [fixedSet, hlength, composition_card]
      · have hset : fixedSet 1 s = ∅ := by
          ext c
          have hne : (1 : ℕ) ≠ s := Ne.symm hs1
          simp [fixedSet, hlength c, hne]
        have hslt : 1 < s := by omega
        rw [hset]
        simp [Nat.choose_eq_zero_of_lt (by omega : 0 < s - 1)]
  | succ k ih =>
      by_cases hs1 : s = 1
      · subst s
        rw [card_fixedSet_succ (k + 1) 1 (by omega) (by omega)]
        rw [fixedSet_zero (k + 1) (by omega)]
        simp [ih 1 (by omega)]
      · have hsPred : 0 < s - 1 := by omega
        obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := by
          use s - 2
          omega
        rw [card_fixedSet_succ (k + 1) (t + 2) (by omega) (by omega)]
        rw [ih (t + 2) (by omega) (by omega),
          ih (t + 2 - 1) (by omega) (by omega)]
        simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
        have hsub1 : t + 2 - 1 = t + 1 := by omega
        rw [hsub1, Nat.add_one_sub_one]
        have hchoose := Nat.choose_succ_succ k t
        simpa [Nat.succ_eq_add_one, Nat.add_comm] using hchoose.symm
end CollatzEndpointTransport.FixedTotal
