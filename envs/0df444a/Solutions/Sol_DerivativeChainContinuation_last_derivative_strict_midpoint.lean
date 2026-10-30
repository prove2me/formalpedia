-- Prove2me | solution 1 for DerivativeChainContinuation.last_derivative_strict_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:37:57.382599+00:00
-- url     : https://prove2.me/submissions/a6962fa0-66e3-49a0-953b-c2f66320467e

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators







theorem realRootProduct_eval {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    (realRootProduct a).eval (a i) = 0 := by
  simp only [realRootProduct, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)




end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators

theorem realRootProduct_log_derivative {n : ℕ} (a : Fin n → ℝ) (x : ℝ)
    (hx : ∀ i, x ≠ a i) :
    (realRootProduct a).derivative.eval x =
      (realRootProduct a).eval x * ∑ i, 1 / (x-a i) := by
  classical
  simp only [realRootProduct, derivative_prod_finset, derivative_X_sub_C, mul_one,
    eval_finsetSum, eval_prod, eval_sub, eval_X, eval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_one_div]
  apply (eq_div_iff (sub_ne_zero.mpr (hx i))).2
  simpa [div_eq_mul_inv] using
    (Finset.prod_erase_mul (Finset.univ : Finset (Fin n)) (fun j => x-a j) hi)

theorem last_derivative_above_penultimate (n : ℕ) (a : Fin (n+3) → ℝ)
    (b : Fin (n+2) → ℝ) (hb : Monotone b)
    (hder : (realRootProduct a).derivative = C (n+3 : ℝ)*realRootProduct b)
    (hgap : a (Fin.last (n+1)).castSucc < a (Fin.last (n+2))) :
    a (Fin.last (n+1)).castSucc < b (Fin.last (n+1)) := by
  obtain ⟨x,hx,hroot⟩ := exists_deriv_eq_zero hgap
    (realRootProduct a).continuousOn
    ((realRootProduct_eval a _).trans (realRootProduct_eval a _).symm)
  have hz : (realRootProduct a).derivative.eval x = 0 := by
    simpa only [Polynomial.deriv] using hroot
  rw [hder,eval_mul,eval_C] at hz
  have hp : (realRootProduct b).eval x=0 :=
    (mul_eq_zero.mp hz).resolve_left (by positivity)
  simp only [realRootProduct,eval_prod,eval_sub,eval_X,eval_C] at hp
  obtain ⟨i,_,hi⟩ := Finset.prod_eq_zero_iff.mp hp
  have hm := hb (Fin.le_last i)
  exact hx.1.trans_le (by simpa [sub_eq_zero.mp hi] using hm)



























end DerivativeChainContinuation

theorem solution (n : ℕ) (a : Fin (n+3) → ℝ)
    (b : Fin (n+2) → ℝ) (ha : Monotone a) (hb : Monotone b)
    (hinter : ∀ i : Fin (n+2), a i.castSucc ≤ b i ∧ b i ≤ a i.succ)
    (hder : (realRootProduct a).derivative = C (n+3 : ℝ)*realRootProduct b)
    (hgap : a (Fin.last (n+1)).castSucc < a (Fin.last (n+2))) :
    (a (Fin.last (n+1)).castSucc+a (Fin.last (n+2)))/2 <
      b (Fin.last (n+1)) := by
  let y := b (Fin.last (n+1))
  let A := a (Fin.last (n+1)).castSucc
  let B := a (Fin.last (n+2))
  have hyA : A<y := last_derivative_above_penultimate n a b hb hder hgap
  have hyB : y≤B := by simpa [y,B] using (hinter (Fin.last (n+1))).2
  by_cases he : y=B
  · change (A+B)/2<y
    change A<B at hgap
    linarith
  have hyB' : y<B := lt_of_le_of_ne hyB he
  have hlower (i : Fin (n+2)) : a i.castSucc ≤ A := ha (by exact_mod_cast Fin.le_last i)
  have hnonzero (i : Fin (n+3)) : y≠a i := by
    induction i using Fin.lastCases with
    | last => exact ne_of_lt hyB'
    | cast i => exact ne_of_gt ((hlower i).trans_lt hyA)
  have hroot : (realRootProduct a).derivative.eval y=0 := by
    rw [hder,eval_mul,eval_C,realRootProduct_eval,mul_zero]
  have hprod : (realRootProduct a).eval y≠0 := by
    simp only [realRootProduct,eval_prod,eval_sub,eval_X,eval_C]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hnonzero i))
  rw [realRootProduct_log_derivative a y hnonzero] at hroot
  have hs := (mul_eq_zero.mp hroot).resolve_left hprod
  rw [Fin.sum_univ_castSucc] at hs
  have hpos (i : Fin (n+2)) : 0<1/(y-a i.castSucc) :=
    one_div_pos.mpr (sub_pos.mpr ((hlower i).trans_lt hyA))
  have hsum : 1/(y-A) < ∑ i : Fin (n+2),1/(y-a i.castSucc) := by
    change 1/(y-a (Fin.last (n+1)).castSucc) < _
    apply Finset.single_lt_sum (f:=fun i : Fin (n+2) => 1/(y-a i.castSucc))
      (s:=Finset.univ) (i:=Fin.last (n+1)) (j:=0)
    · intro hh
      have := congrArg Fin.val hh
      simp only [Fin.val_zero,Fin.val_last] at this
      omega
    · simp
    · simp
    · exact hpos 0
    · intro k _ _
      exact (hpos k).le
  have hinv : 1/(y-A) < 1/(B-y) := by
    have hneg : 1/(y-B) = -(1/(B-y)) := by
      rw [show y-B=-(B-y) by ring]
      simp only [one_div, inv_neg]
    change (∑ i : Fin (n+2),1/(y-a i.castSucc))+1/(y-B)=0 at hs
    rw [hneg] at hs
    linarith
  have hden : B-y < y-A := (one_div_lt_one_div (sub_pos.mpr hyA)
    (sub_pos.mpr hyB')).mp hinv
  change (A+B)/2<y
  linarith
