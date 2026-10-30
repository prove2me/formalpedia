-- Prove2me | solution 1 for DerivativeChainContinuation.positiveQuotient_weighted
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:16:10.881853+00:00
-- url     : https://prove2.me/submissions/313c4306-c249-46e6-980b-d9f6db960540

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
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
open Polynomial DerivativeChainPrivate
open scoped BigOperators



theorem positiveQuotient_eval_ne_of_nonpos (Q : Polynomial ℝ) (hQ : PositiveQuotient Q)
    (x : ℝ) (hx : x≤0) : Q.eval x≠0 := by
  intro h
  have hp := hQ.2.2 x ((mem_roots hQ.1).mpr h)
  linarith




















end DerivativeChainContinuation



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial

theorem real_splits_derivative (p : Polynomial ℝ) (hp : p.Splits) :
    p.derivative.Splits := by
  apply Polynomial.splits_iff_card_roots.mpr
  have hcount := p.card_roots_le_derivative
  have hdegree := Polynomial.natDegree_derivative p
  have hbound := Polynomial.card_roots' p.derivative
  have hsplit := hp.natDegree_eq_card_roots
  omega

theorem weighted_derivative_factor (q : Polynomial ℝ) (r k : ℕ) :
    (X ^ (r + 1) * q ^ (k + 1)).derivative =
      X ^ r * q ^ k * (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative) := by
  simp only [derivative_mul, derivative_pow, derivative_X, mul_one,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [pow_succ q k, pow_succ X r]
  ring

theorem real_splits_weighted_derivative (q : Polynomial ℝ) (hq : q.Splits)
    (r k : ℕ) :
    (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).Splits := by
  by_cases hqzero : q = 0
  · simp [hqzero, Polynomial.Splits.zero]
  let b : Polynomial ℝ := C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative
  by_cases hb : b = 0
  · simpa only [b, hb] using (Polynomial.Splits.zero : (0 : Polynomial ℝ).Splits)
  have hs := real_splits_derivative (X ^ (r + 1) * q ^ (k + 1))
    ((Polynomial.Splits.X_pow (r + 1)).mul (hq.pow (k + 1)))
  rw [weighted_derivative_factor] at hs
  have hne : X ^ r * q ^ k * b ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hqzero)) hb
  exact hs.of_dvd hne ⟨X ^ r * q ^ k, by ring⟩



theorem weighted_negative_parent (q : Polynomial ℝ) (hq : q ≠ 0) (hs : q.Splits)
    (r k : ℕ) (y : ℝ) (hy : y < 0)
    (hz : (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).eval y = 0) :
    ∃ x ∈ q.roots, x ≤ y := by
  classical
  by_contra h
  push Not at h
  have hqy : q.eval y ≠ 0 := by
    intro heq
    have hm := (Polynomial.mem_roots hq).mpr heq
    exact (not_lt_of_ge (le_refl y)) (h y hm)
  let s := (q.roots.map fun x => 1 / (y - x)).sum
  have hsnonpos : s ≤ 0 := by
    have hneg : 0 ≤ (q.roots.map fun x => -(1 / (y - x))).sum := by
      apply Multiset.sum_nonneg
      intro a ha
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
      exact neg_nonneg.mpr (le_of_lt (one_div_neg.mpr (sub_neg.mpr (h x hx))))
    have heq : (q.roots.map fun x => -(1 / (y - x))).sum = -s := by
      simp [s, Multiset.sum_map_neg]
    linarith
  have hd : q.derivative.eval y = q.eval y * s := hs.eval_derivative_eq_eval_mul_sum hqy
  simp only [eval_add, eval_mul, eval_C, eval_X] at hz
  rw [hd] at hz
  have heq : q.eval y * ((r + 1 : ℝ) + (k + 1 : ℝ) * y * s) = 0 := by
    nlinarith [hz]
  have hb := (mul_eq_zero.mp heq).resolve_left hqy
  have hprod : 0 ≤ (k + 1 : ℝ) * y * s :=
    mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hy.le)
      hsnonpos
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  nlinarith





end DerivativeChainPrivate

theorem solution (Q : Polynomial ℝ) (hQ : PositiveQuotient Q)
    (r k : ℕ) :
    PositiveQuotient (C (r+1 : ℝ)*Q+C (k+1 : ℝ)*X*Q.derivative) := by
  let V := C (r+1 : ℝ)*Q+C (k+1 : ℝ)*X*Q.derivative
  have hQ0 := positiveQuotient_eval_ne_of_nonpos Q hQ 0 le_rfl
  have hV0 : V.eval 0≠0 := by
    simpa only [V,eval_add,eval_mul,eval_C,eval_X,mul_zero,zero_mul,add_zero] using
      mul_ne_zero (show (r+1 : ℝ)≠0 by positivity) hQ0
  have hV : V≠0 := by intro h; simp [h] at hV0
  refine ⟨hV,real_splits_weighted_derivative Q hQ.2.1 r k,?_⟩
  intro y hy
  have hyroot : V.eval y=0 := (mem_roots hV).mp hy
  by_contra hn
  have hnonpos : y≤0 := le_of_not_gt hn
  by_cases hy0 : y=0
  · subst y; exact hV0 hyroot
  · have hyneg : y<0 := lt_of_le_of_ne hnonpos hy0
    obtain ⟨x,hx,hxy⟩ := weighted_negative_parent Q hQ.1 hQ.2.1 r k y hyneg hyroot
    have hxpos := hQ.2.2 x hx
    linarith
