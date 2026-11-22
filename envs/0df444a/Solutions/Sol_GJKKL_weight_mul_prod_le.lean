-- Prove2me | solution 1 for GJKKL.weight_mul_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:06:29.757253+00:00
-- url     : https://prove2.me/submissions/8539df00-5b21-460b-baf7-0a58cdf6ad41

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_Greedy_Counting
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_greedyKernel_K
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
public import Theorems.Thm_GJKKL_weight_cons_of_mem
attribute [local simp] GJKKL.History.aliveBefore_cons
attribute [local simp] GJKKL.History.aliveBefore_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.isGreedySeq_cons
attribute [local simp] GJKKL.isGreedySeq_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) :
    ∀ h : List (Finset V), ManyAvail H g h →
      weight (greedyKernel H) h * ∏ i ∈ range h.length, g i ≤ 1
  | [], _ => by simp
  | a :: h, hal => by
    by_cases ha : a ∈ avail H h
    · rw [weight_cons_of_mem ha, List.length_cons, prod_range_succ]
      have ih := solution H g hg h hal.1
      have hcard : 0 < ((avail H h).card : ℝ) := by exact_mod_cast card_pos.mpr ⟨a, ha⟩
      have hgle : g h.length ≤ (avail H h).card := hal.2
      have h1 : g h.length / (avail H h).card ≤ 1 := (div_le_one hcard).mpr hgle
      calc weight (greedyKernel H) h / (avail H h).card * ((∏ i ∈ range h.length, g i) *
            g h.length)
          = (weight (greedyKernel H) h * ∏ i ∈ range h.length, g i) *
              (g h.length / (avail H h).card) := by ring
        _ ≤ 1 * 1 := mul_le_mul ih h1 (div_nonneg (hg _) hcard.le) zero_le_one
        _ = 1 := one_mul 1
    · rw [weight_cons, greedyKernel_K, if_neg ha, mul_zero, zero_mul]
      exact zero_le_one
end GJKKL
