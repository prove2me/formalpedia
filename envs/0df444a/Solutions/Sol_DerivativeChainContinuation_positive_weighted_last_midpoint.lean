-- Prove2me | solution 1 for DerivativeChainContinuation.positive_weighted_last_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:30:35.886212+00:00
-- url     : https://prove2.me/submissions/5b7c86e3-9996-422a-9479-053dd5011659

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveWeightedMidpoint
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





























end DerivativeChainContinuation



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial



theorem weighted_derivative_factor (q : Polynomial ℝ) (r k : ℕ) :
    (X ^ (r + 1) * q ^ (k + 1)).derivative =
      X ^ r * q ^ k * (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative) := by
  simp only [derivative_mul, derivative_pow, derivative_X, mul_one,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [pow_succ q k, pow_succ X r]
  ring











end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators



theorem positive_real_power_derivative (s k : ℕ) (Q : Polynomial ℝ) (hk : 1≤k) :
    X*(X^s*Q^k).derivative=X^s*Q^(k-1)*positiveWeighted s k Q := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
  cases s with
  | zero => simp [positiveWeighted,derivative_pow]; ring
  | succ s =>
    rw [weighted_derivative_factor Q s j]
    simp only [positiveWeighted,Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,
      pow_succ (X : Polynomial ℝ) s]
    ring

theorem positive_weighted_gap_root (s k : ℕ) (Q : Polynomial ℝ) (hk : 1≤k)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hQa : Q.eval a=0) (hQb : Q.eval b=0)
    (hgap : ∀ x : ℝ,a<x → x<b → Q.eval x≠0) :
    ∃ x : ℝ,a<x ∧ x<b ∧ (positiveWeighted s k Q).eval x=0 := by
  let g := X^s*Q^k
  have hga : g.eval a=0 := by simp only [g,eval_mul,eval_pow,eval_X,hQa,zero_pow (by omega : k≠0),mul_zero]
  have hgb : g.eval b=0 := by simp only [g,eval_mul,eval_pow,eval_X,hQb,zero_pow (by omega : k≠0),mul_zero]
  obtain ⟨x,hx,hder⟩ := exists_deriv_eq_zero hab g.continuousOn (hga.trans hgb.symm)
  have hd : g.derivative.eval x=0 := by simpa only [Polynomial.deriv] using hder
  have he := congrArg (fun p : Polynomial ℝ => p.eval x) (positive_real_power_derivative s k Q hk)
  simp only [eval_mul,eval_X,eval_pow] at he
  change x*g.derivative.eval x=x^s*Q.eval x^(k-1)*(positiveWeighted s k Q).eval x at he
  rw [hd,mul_zero] at he
  have hp : x^s*Q.eval x^(k-1)≠0 := mul_ne_zero
    (pow_ne_zero _ (ne_of_gt (ha.trans hx.1))) (pow_ne_zero _ (hgap x hx.1 hx.2))
  exact ⟨x,hx.1,hx.2,(mul_eq_zero.mp he.symm).resolve_left hp⟩

theorem positive_product_gap_eval_ne (d : ℕ) (a : Fin (d+2) → ℝ) (ha : Monotone a)
    (x : ℝ) (hxA : a (Fin.last d).castSucc<x) (hxB : x<a (Fin.last (d+1))) :
    (realRootProduct a).eval x≠0 := by
  simp only [realRootProduct,eval_prod,eval_sub,eval_X,eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply sub_ne_zero.mpr
  induction i using Fin.lastCases with
  | last => exact ne_of_lt hxB
  | cast i =>
    have hm : a i.castSucc≤a (Fin.last d).castSucc := ha (by exact_mod_cast Fin.le_last i)
    exact ne_of_gt (hm.trans_lt hxA)




end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators







theorem realRootProduct_eval {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    (realRootProduct a).eval (a i) = 0 := by
  simp only [realRootProduct, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)




end DerivativeChainContinuation

theorem solution (d s k : ℕ) (a : Fin (d+2) → ℝ)
    (ha : Monotone a) (hpositive : ∀ i,0<a i) (hk : 1≤k)
    (hgap : a (Fin.last d).castSucc<a (Fin.last (d+1)))
    (t : ℝ) (ht : 0<t) (hroot : (positiveWeighted s k (realRootProduct a)).eval t=0)
    (hmax : ∀ x : ℝ,0<x → (positiveWeighted s k (realRootProduct a)).eval x=0 → x≤t) :
    (a (Fin.last d).castSucc+a (Fin.last (d+1)))/2≤t := by
  let A := a (Fin.last d).castSucc
  let B := a (Fin.last (d+1))
  by_cases htB : B≤t
  · change (A+B)/2≤t
    change A<B at hgap
    linarith
  have htB' : t<B := lt_of_not_ge htB
  obtain ⟨x,hxA,hxB,hxroot⟩ := positive_weighted_gap_root s k (realRootProduct a) hk A B
    (hpositive _) hgap (realRootProduct_eval a _) (realRootProduct_eval a _)
    (fun x hxA hxB => positive_product_gap_eval_ne d a ha x hxA hxB)
  have hxt := hmax x ((hpositive _).trans hxA) hxroot
  have hAt : A<t := hxA.trans_le hxt
  have hnonzero (i : Fin (d+2)) : t≠a i := by
    induction i using Fin.lastCases with
    | last => exact ne_of_lt htB'
    | cast i =>
      have hm : a i.castSucc≤A := ha (by exact_mod_cast Fin.le_last i)
      exact ne_of_gt (hm.trans_lt hAt)
  have hQne := positive_product_gap_eval_ne d a ha t hAt htB'
  have hlog := realRootProduct_log_derivative a t hnonzero
  have he : (s : ℝ)+(k : ℝ)*t*(∑ i : Fin (d+2),1/(t-a i))=0 := by
    simp only [positiveWeighted,eval_add,eval_mul,eval_C,eval_X] at hroot
    rw [hlog] at hroot
    have hf : (realRootProduct a).eval t*
        ((s : ℝ)+(k : ℝ)*t*(∑ i : Fin (d+2),1/(t-a i)))=0 := by nlinarith [hroot]
    exact (mul_eq_zero.mp hf).resolve_left hQne
  rw [Fin.sum_univ_castSucc] at he
  have hpos (i : Fin (d+1)) : 0≤1/(t-a i.castSucc) := by
    have hm : a i.castSucc≤A := ha (by exact_mod_cast Fin.le_last i)
    exact (one_div_pos.mpr (sub_pos.mpr (hm.trans_lt hAt))).le
  have hsum : 1/(t-A)≤∑ i : Fin (d+1),1/(t-a i.castSucc) := by
    exact Finset.single_le_sum (fun i _ => hpos i) (Finset.mem_univ (Fin.last d))
  have hnegative : 1/(t-B)=-(1/(B-t)) := by
    rw [show t-B=-(B-t) by ring]
    simp only [one_div,inv_neg]
  change (s : ℝ)+(k : ℝ)*t*((∑ i : Fin (d+1),1/(t-a i.castSucc))+1/(t-B))=0 at he
  rw [hnegative] at he
  have hkt : 0<(k : ℝ)*t := mul_pos (by exact_mod_cast (show 0<k by omega)) ht
  have hsumle : (∑ i : Fin (d+1),1/(t-a i.castSucc))≤1/(B-t) := by
    have hs : 0≤(s : ℝ) := Nat.cast_nonneg s
    nlinarith
  have hcomp : 1/(t-A)≤1/(B-t) := hsum.trans hsumle
  have hden : B-t≤t-A := (one_div_le_one_div (sub_pos.mpr hAt) (sub_pos.mpr htB')).mp hcomp
  change (A+B)/2≤t
  linarith
