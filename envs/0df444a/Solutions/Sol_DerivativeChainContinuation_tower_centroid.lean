-- Prove2me | solution 1 for DerivativeChainContinuation.tower_centroid
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:51:27.459095+00:00
-- url     : https://prove2.me/submissions/a8516edf-adc5-400e-ba64-412d7805f6b0

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTower
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

theorem solution (r : RealRows) (n : ℕ)
    (hstep : ∀ k<n,RealRowStep r k) :
    ∑ i,r n i = (n+1 : ℝ)*r 0 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := real_step_mean r n (hstep n (by omega))
    have hi := ih (fun k hk => hstep k (by omega))
    rw [hi] at h
    have hn : (n+1 : ℝ)≠0 := by positivity
    have he : (n+1 : ℝ)*((n+2 : ℝ)*r 0 0 - ∑ i,r (n+1) i)=0 := by
      linear_combination h
    have hh := (mul_eq_zero.mp he).resolve_left hn
    push_cast
    linarith
