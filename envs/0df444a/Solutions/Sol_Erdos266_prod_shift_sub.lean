-- Prove2me | solution 1 for Erdos266.prod_shift_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:40:39.627893+00:00
-- url     : https://prove2.me/submissions/c255cea6-a259-4d73-b570-11403f1282ac

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_SlopeLemma

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (i : ℕ) (N x : ℝ) :
    (∏ j ∈ range i, (N + (x + (tSeq j : ℝ)))) - (∏ j ∈ range i, (N + (tSeq j : ℝ)))
      = x * ∑ k ∈ range i, ∏ j ∈ (range i).erase k,
          (N + if j < k then x + (tSeq j : ℝ) else (tSeq j : ℝ)) := by
  set H : ℕ → ℝ := fun k =>
    ∏ j ∈ range i, (N + if j < k then x + (tSeq j : ℝ) else (tSeq j : ℝ)) with hH
  have hH0 : H 0 = ∏ j ∈ range i, (N + (tSeq j : ℝ)) := by
    simp [hH]
  have hHi : H i = ∏ j ∈ range i, (N + (x + (tSeq j : ℝ))) := by
    refine prod_congr rfl fun j hj => ?_
    rw [if_pos (mem_range.mp hj)]
  have hstep : ∀ k ∈ range i, H (k + 1) - H k
      = x * ∏ j ∈ (range i).erase k,
          (N + if j < k then x + (tSeq j : ℝ) else (tSeq j : ℝ)) := by
    intro k hk
    have h1 : H (k + 1) = (N + (x + (tSeq k : ℝ)))
        * ∏ j ∈ (range i).erase k,
            (N + if j < k then x + (tSeq j : ℝ) else (tSeq j : ℝ)) := by
      rw [hH]
      simp only
      rw [← mul_prod_erase (range i) _ hk]
      congr 1
      · rw [if_pos (Nat.lt_succ_self k)]
      · refine prod_congr rfl fun j hj => ?_
        have hjk : j ≠ k := (mem_erase.mp hj).1
        by_cases h : j < k
        · rw [if_pos h, if_pos (Nat.lt_succ_of_lt h)]
        · rw [if_neg h, if_neg (by omega)]
    have h2 : H k = (N + (tSeq k : ℝ))
        * ∏ j ∈ (range i).erase k,
            (N + if j < k then x + (tSeq j : ℝ) else (tSeq j : ℝ)) := by
      rw [hH]
      simp only
      rw [← mul_prod_erase (range i) _ hk]
      congr 1
      rw [if_neg (lt_irrefl k)]
    rw [h1, h2]
    ring
  calc (∏ j ∈ range i, (N + (x + (tSeq j : ℝ))))
        - (∏ j ∈ range i, (N + (tSeq j : ℝ)))
      = H i - H 0 := by rw [hH0, hHi]
  _ = ∑ k ∈ range i, (H (k + 1) - H k) := (sum_range_sub H i).symm
  _ = ∑ k ∈ range i, x * ∏ j ∈ (range i).erase k,
        (N + if j < k then x + (tSeq j : ℝ) else (tSeq j : ℝ)) :=
      sum_congr rfl hstep
  _ = x * ∑ k ∈ range i, ∏ j ∈ (range i).erase k,
        (N + if j < k then x + (tSeq j : ℝ) else (tSeq j : ℝ)) := by
      rw [mul_sum]
end Erdos266
