-- Prove2me | solution 1 for GJKKL.prob_mul_prod_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:56.402213+00:00
-- url     : https://prove2.me/submissions/66a56bbf-5271-4b7f-b5aa-e695992711ca

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_Greedy_Counting
public import Theorems.Thm_GJKKL_weight_mul_prod_le
public import Theorems.Thm_GJKKL_card_greedySeq_le
public import Theorems.Thm_GJKKL_History_mem_hist
public import Theorems.Thm_GJKKL_weight_eq_zero_of_not


set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (hne : ∀ e ∈ H, e.Nonempty)
    (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) (m : ℕ) :
    prob (greedyKernel H) m (ManyAvail H g) * ∏ i ∈ range m, g i ≤
      (m.factorial : ℝ) * (matchingsOfSize H m).card := by
  classical
  have h1 : prob (greedyKernel H) m (ManyAvail H g) * ∏ i ∈ range m, g i ≤
      (((hist (Finset V) m).filter (IsGreedySeq H)).card : ℝ) := by
    unfold History.prob History.expect
    rw [sum_mul, card_filter, Nat.cast_sum]
    refine sum_le_sum fun h hh => ?_
    rw [mem_hist] at hh
    beta_reduce
    by_cases hv : IsGreedySeq H h
    · rw [if_pos hv, Nat.cast_one]
      by_cases hal : ManyAvail H g h
      · rw [if_pos hal, mul_one, ← hh]
        exact weight_mul_prod_le H g hg h hal
      · rw [if_neg hal, mul_zero, zero_mul]; exact zero_le_one
    · rw [if_neg hv, Nat.cast_zero, weight_eq_zero_of_not hv, zero_mul, zero_mul]
  refine h1.trans ?_
  exact_mod_cast card_greedySeq_le H hne m
end GJKKL
