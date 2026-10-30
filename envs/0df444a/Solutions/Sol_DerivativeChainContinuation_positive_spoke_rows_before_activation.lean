-- Prove2me | solution 1 for DerivativeChainContinuation.positive_spoke_rows_before_activation
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:18:04.516242+00:00
-- url     : https://prove2.me/submissions/6055b4ac-7bbd-400f-aaed-b19a58270770

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positiveQuotient_weighted
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators



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











theorem derivative_negative_parent (q : Polynomial ℝ) (hq : q ≠ 0) (hs : q.Splits)
    (hdeg : 0 < q.natDegree) (y : ℝ) (hz : q.derivative.eval y = 0) :
    ∃ x ∈ q.roots, x ≤ y := by
  classical
  by_contra h
  push Not at h
  have hqy : q.eval y ≠ 0 := by
    intro heq
    exact (lt_irrefl y) (h y ((Polynomial.mem_roots hq).mpr heq))
  let s := (q.roots.map fun x => -(1 / (y - x))).sum
  have hterms : ∀ a ∈ (q.roots.map fun x => -(1 / (y - x))), 0 ≤ a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
    exact neg_nonneg.mpr (one_div_neg.mpr (sub_neg.mpr (h x hx))).le
  have hnonempty : q.roots ≠ 0 := by
    intro heq
    have hc := hs.natDegree_eq_card_roots
    simp only [heq, Multiset.card_zero] at hc
    omega
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hnonempty
  have hle : -(1 / (y - x)) ≤ s :=
    Multiset.single_le_sum hterms _ (Multiset.mem_map.mpr ⟨x, hx, rfl⟩)
  have hd := hs.eval_derivative_eq_eval_mul_sum hqy
  rw [hz] at hd
  have hs0 : s = 0 := by
    have heq : (q.roots.map fun x => -(1 / (y - x))).sum =
        -(q.roots.map fun x => 1 / (y - x)).sum := by simp [Multiset.sum_map_neg]
    dsimp only [s]
    rw [heq, (mul_eq_zero.mp hd.symm).resolve_left hqy, neg_zero]
  have hpos := neg_pos.mpr (one_div_neg.mpr (sub_neg.mpr (h x hx)))
  linarith

end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators





theorem positiveQuotient_C_mul (Q : Polynomial ℝ) (hQ : PositiveQuotient Q)
    (c : ℝ) (hc : c≠0) : PositiveQuotient (C c*Q) := by
  refine ⟨mul_ne_zero (C_ne_zero.mpr hc) hQ.1,hQ.2.1.C_mul c,?_⟩
  intro x hx
  exact hQ.2.2 x (by simpa only [roots_C_mul Q hc] using hx)

theorem positiveQuotient_derivative (Q : Polynomial ℝ) (hQ : PositiveQuotient Q)
    (hdegree : 0<Q.natDegree) : PositiveQuotient Q.derivative := by
  have hd : Q.derivative≠0 := derivative_ne_zero.mpr (by omega)
  refine ⟨hd,real_splits_derivative Q hQ.2.1,?_⟩
  intro y hy
  obtain ⟨x,hx,hxy⟩ := derivative_negative_parent Q hQ.1 hQ.2.1 hdegree y
    ((mem_roots hd).mp hy)
  exact (hQ.2.2 x hx).trans_le hxy





theorem complex_iterate_derivative_natDegree (p : Polynomial ℂ) (j : ℕ) :
    (derivative^[j] p).natDegree=p.natDegree-j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',natDegree_derivative,ih]
    omega










end DerivativeChainContinuation



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial



theorem spoke_derivative_succ (k r : ℕ) (q : Polynomial ℝ) :
    (spokePoly (k + 1) (r + 1) q).derivative =
      spokePoly (k + 1) r
        (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative) := by
  simp only [spokePoly, derivative_mul, derivative_pow, derivative_X, mul_one,
    Nat.add_sub_cancel, derivative_comp, derivative_map, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.add_comp,
    Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
  rw [pow_succ (X : Polynomial ℂ) r, pow_succ (X : Polynomial ℂ) k]
  simp only [map_add, map_natCast, map_one]
  push_cast
  ring

theorem spoke_derivative_zero (k : ℕ) (q : Polynomial ℝ) :
    (spokePoly (k + 1) 0 q).derivative =
      spokePoly (k + 1) k (C (k + 1 : ℝ) * q.derivative) := by
  simp only [spokePoly, pow_zero, one_mul, derivative_comp, derivative_pow,
    derivative_X, mul_one, Nat.add_sub_cancel, derivative_map,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.mul_comp, Polynomial.C_comp]
  simp only [map_add, map_natCast, map_one]
  push_cast
  ring

theorem spoke_natDegree (k r : ℕ) (q : Polynomial ℝ) (hq : q ≠ 0) (hk : 0 < k) :
    (spokePoly k r q).natDegree = r + k * q.natDegree := by
  have hmap : q.map Complex.ofRealHom ≠ 0 := Polynomial.map_ne_zero hq
  have hcomp : (q.map Complex.ofRealHom).comp (X ^ k) ≠ 0 := by
    rw [ne_eq, Polynomial.comp_eq_zero_iff]
    simp only [hmap, false_or]
    intro h
    have hdegree := congrArg Polynomial.natDegree h.2
    simp only [natDegree_X_pow, natDegree_C] at hdegree
    omega
  rw [spokePoly, natDegree_mul (pow_ne_zero _ X_ne_zero) hcomp,
    natDegree_X_pow, natDegree_comp, natDegree_map, natDegree_X_pow]
  ring









end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem positive_weighted_natDegree (r k : ℕ) (Q : Polynomial ℝ)
    (hQ : PositiveQuotient Q) :
    (C (r+1 : ℝ)*Q+C (k+1 : ℝ)*X*Q.derivative).natDegree=Q.natDegree := by
  let V := C (r+1 : ℝ)*Q+C (k+1 : ℝ)*X*Q.derivative
  have hV := positiveQuotient_weighted Q hQ r k
  have h := congrArg Polynomial.natDegree (spoke_derivative_succ k r Q)
  rw [natDegree_derivative,spoke_natDegree _ _ _ hQ.1 (by omega),
    spoke_natDegree _ _ _ hV.1 (by omega)] at h
  have he : (k+1)*V.natDegree=(k+1)*Q.natDegree := by dsimp [V]; omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) he

theorem positive_spoke_derivative_above_activation (k r : ℕ) (Q : Polynomial ℝ)
    (hk : 2≤k) (hQ : PositiveQuotient Q) (hQdegree : 0<Q.natDegree)
    (hdegree : k<(spokePoly k r Q).natDegree) :
    ∃ s : ℕ, ∃ V : Polynomial ℝ, PositiveQuotient V ∧ 0<V.natDegree ∧
      (spokePoly k r Q).derivative=spokePoly k s V := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
  cases r with
  | zero =>
    have hdeg := spoke_natDegree (j+1) 0 Q hQ.1 (by omega)
    have hQdeg : 2≤Q.natDegree := by
      by_contra hn
      have he : Q.natDegree=1 := by omega
      rw [hdeg,he] at hdegree
      omega
    have hPQ := positiveQuotient_derivative Q hQ (by omega)
    refine ⟨j,C (j+1 : ℝ)*Q.derivative,
      positiveQuotient_C_mul _ hPQ _ (by positivity),?_,spoke_derivative_zero j Q⟩
    rw [natDegree_C_mul (show (j+1 : ℝ)≠0 by positivity),natDegree_derivative]
    omega
  | succ r =>
    refine ⟨r,C (r+1 : ℝ)*Q+C (j+1 : ℝ)*X*Q.derivative,
      positiveQuotient_weighted Q hQ r j,?_,spoke_derivative_succ j r Q⟩
    rw [positive_weighted_natDegree r j Q hQ]
    exact hQdegree













end DerivativeChainContinuation

theorem solution (n k r : ℕ) (Q : Polynomial ℝ)
    (hk : 2≤k) (hQ : PositiveQuotient Q) (hQdegree : 0<Q.natDegree)
    (hdegree : (spokePoly k r Q).natDegree=n+1) :
    ∀ j, j+k≤n+1 → ∃ s : ℕ, ∃ V : Polynomial ℝ,
      PositiveQuotient V ∧ 0<V.natDegree ∧
      derivative^[j] (spokePoly k r Q)=spokePoly k s V := by
  intro j hj
  induction j with
  | zero => exact ⟨r,Q,hQ,hQdegree,rfl⟩
  | succ j ih =>
    obtain ⟨s,V,hV,hVdegree,heq⟩ := ih (by omega)
    have hd : k<(spokePoly k s V).natDegree := by
      rw [←heq,complex_iterate_derivative_natDegree,hdegree]
      omega
    obtain ⟨t,W,hW,hWdegree,hder⟩ :=
      positive_spoke_derivative_above_activation k s V hk hV hVdegree hd
    refine ⟨t,W,hW,hWdegree,?_⟩
    rw [Function.iterate_succ_apply',heq,hder]
