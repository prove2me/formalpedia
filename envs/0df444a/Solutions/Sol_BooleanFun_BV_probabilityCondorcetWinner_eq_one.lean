-- Prove2me | solution 1 for BooleanFun.BV.probabilityCondorcetWinner_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:13:10.810085+00:00
-- url     : https://prove2.me/submissions/9ca16087-2803-4e68-980d-d9c06ef39f02

import Definitions.Def_BooleanFun_BooleanValued
import Definitions.Def_BooleanFun_Arrow
import Theorems.Thm_BooleanFun_BV__triple_sum_oneOn_consistent_eq
import Theorems.Thm_BooleanFun_oneOn_and


set_option autoImplicit false
noncomputable section
open BooleanFun BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}
namespace BooleanFun.BV
theorem _root_.solution (hc : IsCondorcet f):
    probabilityCondorcetWinner f = 1 := by
  -- 6^n * LHS = ∑ x, ∑ y, ∑ z, ∏ i, oneOn (NAE3 (x i) (y i) (z i))
  have : ∀ x y z : Fin n → Fin 2, NAE3 (f x) (f y) (f z) ∧ VoteConsistent x y z ↔
      VoteConsistent x y z := by
    intro x y z
    specialize hc x y z
    tauto
  unfold probabilityCondorcetWinner
  simp_rw [← oneOn_and, this, _triple_sum_oneOn_consistent_eq]
  simp
end BooleanFun.BV
