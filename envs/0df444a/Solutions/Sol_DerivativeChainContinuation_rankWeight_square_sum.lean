-- Prove2me | solution 1 for DerivativeChainContinuation.rankWeight_square_sum
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:04:46.897241+00:00
-- url     : https://prove2.me/submissions/61116de0-2229-4ff6-8399-756e2e74bfd0

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RankDispersion
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators



theorem rankWeight_sum (m : ℕ) : (∑ i : Fin m,rankWeight m i)=0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    have hw (i : Fin m) : rankWeight (m+1) i.succ=rankWeight m i+1 := by
      simp only [rankWeight,Fin.val_succ,Nat.cast_add,Nat.cast_one]
      ring
    simp_rw [hw]
    rw [Finset.sum_add_distrib,ih]
    simp [rankWeight]








end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (m : ℕ) :
    (∑ i : Fin m,(rankWeight m i)^2)=(m : ℝ)*((m : ℝ)^2-1)/3 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    have hw (i : Fin m) : (rankWeight (m+1) i.succ)^2=
        (rankWeight m i)^2+2*rankWeight m i+1 := by
      simp only [rankWeight,Fin.val_succ,Nat.cast_add,Nat.cast_one]
      ring
    simp_rw [hw]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,rankWeight_sum,ih]
    simp [rankWeight]
    ring
