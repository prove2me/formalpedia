-- Prove2me | solution 1 for DerivativeChainContinuation.positive_spoke_activation_row
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:20:32.241664+00:00
-- url     : https://prove2.me/submissions/f2da07c6-85fb-4f65-a6e0-d481d67d2c11

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_spoke_rows_before_activation
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

theorem solution (n k r : ℕ) (Q : Polynomial ℝ)
    (hk : 2≤k) (hQ : PositiveQuotient Q) (hQdegree : 0<Q.natDegree)
    (hdegree : (spokePoly k r Q).natDegree=n+1) :
    ∃ V : Polynomial ℝ, PositiveQuotient V ∧ V.natDegree=1 ∧
      derivative^[n+1-k] (spokePoly k r Q)=spokePoly k 0 V := by
  have hdeg := spoke_natDegree k r Q hQ.1 (by omega)
  have hle : k≤n+1 := by
    have hh : k≤k*Q.natDegree := Nat.le_mul_of_pos_right k hQdegree
    omega
  obtain ⟨s,V,hV,hVdegree,heq⟩ := positive_spoke_rows_before_activation n k r Q
    hk hQ hQdegree hdegree (n+1-k) (by omega)
  have hd : (spokePoly k s V).natDegree=k := by
    rw [←heq,complex_iterate_derivative_natDegree,hdegree]
    omega
  rw [spoke_natDegree _ _ _ hV.1 (by omega)] at hd
  have hVone : V.natDegree=1 := by
    by_contra hn
    have hh := Nat.mul_le_mul_left k (show 2≤V.natDegree by omega)
    nlinarith
  have hs : s=0 := by rw [hVone,mul_one] at hd; omega
  subst s
  exact ⟨V,hV,hVone,heq⟩
