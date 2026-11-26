-- Prove2me | solution 1 for Erdos266.finSum_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:03:14.722349+00:00
-- url     : https://prove2.me/submissions/69cbbd04-e1f1-43d8-a30d-d6b444149033

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
public import Theorems.Thm_Erdos266_finSum_congr
public import Theorems.Thm_Erdos266_finSum_succ
public import Theorems.Thm_Erdos266_newS_eq_of_lt
public import Theorems.Thm_Erdos266_newS_eq_blk

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {k : ℕ} {st : AlgSt} (h : Inv k st) (i : ℕ) :
    finSum i (k + 1) (newS k st h)
      = finSum i k st.1 + ∑ j : Fin (dOf k),
          f (i + 1) ((((j.val + 1) * bigN k : ℕ) : ℝ) + (blk k st h j : ℝ)) := by
  rw [finSum_succ]
  congr 1
  · exact (finSum_congr fun l hl j _ => (newS_eq_of_lt h (by omega) j).symm).symm
  · rw [← Fin.sum_univ_eq_sum_range
      (fun j => f (i + 1) (elemR (newS k st h) k j)) (dOf k)]
    refine Fintype.sum_congr _ _ fun j => ?_
    rw [elemR, newS_eq_blk h j.isLt]
end Erdos266
