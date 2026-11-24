-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.sourceTail_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:41.974068+00:00
-- url     : https://prove2.me/submissions/6d3eb01a-9b0a-43b3-95bc-028c362d0473

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
public import Theorems.Thm_BalanceSpecification_block_append


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] {Y : ShiftSpace A}
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution (x : Y.carrier) {m n : ℕ} (hmn : m ≤ n) :
    sourceTail x m <:+ sourceTail x n := by
  have hstart : -(n : ℤ) + ((n - m : ℕ) : ℤ) = -(m : ℤ) := by omega
  have h := block_append x.val (-(n : ℤ)) (n - m) m
  rw [Nat.sub_add_cancel hmn, hstart] at h
  exact ⟨block x.val (-(n : ℤ)) (n - m), h.symm⟩
end BalanceSpecification.MarkerExtension
