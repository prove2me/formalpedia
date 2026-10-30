-- Prove2me | solution 1 for DerivativeChainContinuation.real_tower_centered
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T16:53:58.979966+00:00
-- url     : https://prove2.me/submissions/f35685f9-0944-48bf-a9bb-3f9e71fe9f12

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
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

theorem realRootProduct_nextCoeff {n : ℕ} (a : Fin n → ℝ) :
    (realRootProduct a).nextCoeff = -(∑ i,a i) := by
  have h := (realRootProduct_splits a).nextCoeff_eq_neg_sum_roots_of_monic (realRootProduct_monic a)
  simpa only [realRootProduct_roots,Finset.sum_map_val] using h



theorem real_step_mean (r : RealRows) (k : ℕ) (h : RealRowStep r k) :
    (k+2 : ℝ)*(∑ i,r k i) = (k+1 : ℝ)*(∑ i,r (k+1) i) := by
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff k) h.2
  have ha := realRootProduct_nextCoeff (r (k+1))
  have hb := realRootProduct_nextCoeff (r k)
  rw [nextCoeff_of_natDegree_pos (by rw [realRootProduct_degree]; omega),realRootProduct_degree] at ha hb
  simp only [show k+1+1-1=k+1 by omega,show k+1-1=k by omega] at ha hb
  simp only [coeff_derivative,coeff_C_mul] at hc
  rw [ha,hb] at hc
  push_cast at hc
  linarith





end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (r : RealRows) (n : ℕ)
    (hstep : ∀ k<n,RealRowStep r k) (hc : ∑ i,r n i = 0) :
    ∀ k≤n,∑ i,r k i = 0 := by
  induction n with
  | zero =>
    intro k hk
    have hk0 : k=0 := by omega
    subst k
    exact hc
  | succ n ih =>
    have hs := real_step_mean r n (hstep n (by omega))
    rw [hc,mul_zero] at hs
    have hnc : (n+2 : ℝ) ≠ 0 := by positivity
    have hc' : ∑ i,r n i = 0 := (mul_eq_zero.mp hs).resolve_left hnc
    intro k hk
    by_cases he : k=n+1
    · subst k
      exact hc
    · exact ih (fun j hj => hstep j (by omega)) hc' k (by omega)
