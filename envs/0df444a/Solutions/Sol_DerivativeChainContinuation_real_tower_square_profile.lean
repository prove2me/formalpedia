-- Prove2me | solution 1 for DerivativeChainContinuation.real_tower_square_profile
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:02:38.061319+00:00
-- url     : https://prove2.me/submissions/09cb17b7-3662-4ca1-8c8a-567378d27aae

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_real_tower_centered
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators



theorem realRootProduct_monic {n : ℕ} (a : Fin n → ℝ) :
    (realRootProduct a).Monic := Polynomial.monic_prod_X_sub_C a Finset.univ

theorem realRootProduct_degree {n : ℕ} (a : Fin n → ℝ) :
    (realRootProduct a).natDegree = n := by
  unfold realRootProduct
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (a i))]
  simp






end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial

theorem multiset_second_newton {R : Type*} [CommRing R] (s : Multiset R) :
    s.sum^2 = (s.map fun z => z^2).sum + 2*s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    have hmul : (s.map fun x => a*x).sum = a*s.sum := by
      simpa using (Multiset.sum_map_mul_left (s := s) (a := a) (f := id))
    have hs : (a ::ₘ s).esymm 2 = s.esymm 2 + a*s.sum := by
      simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one,
        hmul]
    simp only [Multiset.sum_cons, Multiset.map_cons, hs]
    linear_combination ih

theorem polynomial_second_newton_of_splits {F : Type*} [Field F]
    (p : Polynomial F) (hp : p.Monic) (hsplit : p.Splits)
    (hdeg : 2 ≤ p.natDegree) :
    (p.roots.map fun z => z^2).sum =
      p.roots.sum^2 - 2*p.coeff (p.natDegree-2) := by
  have hc := p.coeff_eq_esymm_roots_of_splits hsplit
    (k := p.natDegree-2) (Nat.sub_le _ _)
  have hd : p.natDegree-(p.natDegree-2)=2 := by omega
  simp only [hp.leadingCoeff, one_mul, hd, neg_one_sq, one_mul] at hc
  rw [hc]
  linear_combination -(multiset_second_newton p.roots)




end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators

theorem realRootProduct_roots {n : ℕ} (a : Fin n → ℝ) :
    (realRootProduct a).roots = Finset.univ.val.map a := by
  have hprod : realRootProduct a =
      ((Finset.univ.val.map a).map fun x => (X-C x : Polynomial ℝ)).prod := by
    simp only [Multiset.map_map,Function.comp_def]
    rfl
  rw [hprod,roots_multiset_prod_X_sub_C]

theorem realRootProduct_splits {n : ℕ} (a : Fin n → ℝ) :
    (realRootProduct a).Splits := by
  apply splits_iff_card_roots.mpr
  simp [realRootProduct_roots,realRootProduct_degree]



theorem realRootProduct_secondCoeff (n : ℕ) (a : Fin (n+2) → ℝ) :
    (∑ i,(a i)^2) = (∑ i,a i)^2-2*(realRootProduct a).coeff n := by
  have h := polynomial_second_newton_of_splits (realRootProduct a)
    (realRootProduct_monic a) (realRootProduct_splits a) (by rw [realRootProduct_degree]; omega)
  simpa only [realRootProduct_roots,Multiset.map_map,Function.comp_def,
    Finset.sum_map_val,realRootProduct_degree,Nat.add_sub_cancel] using h



theorem real_step_square (r : RealRows) (k : ℕ) (h : RealRowStep r (k+1))
    (ha : ∑ i,r (k+2) i = 0) (hb : ∑ i,r (k+1) i = 0) :
    (k+3 : ℝ)*(∑ i,(r (k+1) i)^2) =
      (k+1 : ℝ)*(∑ i,(r (k+2) i)^2) := by
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff k) h.2
  simp only [coeff_derivative,coeff_C_mul] at hc
  have hpa := realRootProduct_secondCoeff (k+1) (r (k+2))
  have hpb := realRootProduct_secondCoeff k (r (k+1))
  rw [ha] at hpa
  rw [hb] at hpb
  simp only [zero_pow (by decide : 2 ≠ 0),zero_sub] at hpa hpb
  rw [hpa,hpb]
  push_cast at hc
  linear_combination 2*hc



end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (r : RealRows) (n : ℕ)
    (hstep : ∀ k<n,RealRowStep r k) (hc : ∑ i,r n i = 0) :
    ∀ k≤n,(n : ℝ)*(n+1)*(∑ i,(r k i)^2) =
      (k : ℝ)*(k+1)*(∑ i,(r n i)^2) := by
  induction n with
  | zero =>
    intro k hk
    have hk0 : k=0 := by omega
    subst k
    simp
  | succ n ih =>
    have hall := real_tower_centered r (n+1) hstep hc
    have hc' := hall n (by omega)
    intro k hk
    by_cases he : k=n+1
    · subst k; rfl
    have hk' : k≤n := by omega
    cases n with
    | zero =>
      have hk0 : k=0 := by omega
      subst k
      have hz : r 0 0=0 := by simpa using hc'
      simp [hz]
    | succ j =>
      have hi := ih (fun l hl => hstep l (by omega)) hc' k hk'
      have hs := real_step_square r j (hstep (j+1) (by omega)) hc hc'
      have hnc : (j+1 : ℝ) ≠ 0 := by positivity
      have hz : (j+1 : ℝ)*(((j : ℝ)+2)*(j+3)*(∑ i,(r k i)^2)-
          (k : ℝ)*(k+1)*(∑ i,(r (j+2) i)^2))=0 := by
        push_cast at hi
        linear_combination (j+3 : ℝ)*hi+(k : ℝ)*(k+1)*hs
      have hzz := (mul_eq_zero.mp hz).resolve_left hnc
      push_cast
      linarith
