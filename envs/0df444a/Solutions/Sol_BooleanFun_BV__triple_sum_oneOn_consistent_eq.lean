-- Prove2me | solution 1 for BooleanFun.BV._triple_sum_oneOn_consistent_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:07:08.265596+00:00
-- url     : https://prove2.me/submissions/f352cd50-6c37-4a76-bbaa-64f87e81a2a1

import Definitions.Def_BooleanFun_BooleanValued
import Definitions.Def_BooleanFun_Arrow
import Theorems.Thm_BooleanFun_oneOn_prod


set_option autoImplicit false
noncomputable section
open BooleanFun BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}
namespace BooleanFun.BV
theorem _root_.solution:
    ∑ x : Fin n → Fin 2, ∑ y : Fin n → Fin 2, ∑ z : Fin n → Fin 2, oneOn (VoteConsistent x y z) = 6^n := by
  unfold VoteConsistent
  simp_rw [← oneOn_prod]
  conv => enter [1, 2, x, 2, y]
          rw [← Fintype.prod_sum (f := fun i ↦ fun c ↦ oneOn (NAE3 (x i) (y i) c))]
  -- = ∑ x, ∏ i, ∑ b, ∑ c, oneOn (NAE3 (x i) b c)
  conv => enter [1, 2, x]
          rw [← Fintype.prod_sum (f := fun i ↦ fun b ↦ ∑ c, oneOn (NAE3 (x i) b c))]
  -- = ∏ i, ∑ a, ∑ b, ∑ c, oneOn (NAE3 a b c)
  rw [← Fintype.prod_sum (f := fun _ ↦ fun a ↦ ∑ b, ∑ c, oneOn (NAE3 a b c))]
  -- = 6^n
  norm_num
end BooleanFun.BV
