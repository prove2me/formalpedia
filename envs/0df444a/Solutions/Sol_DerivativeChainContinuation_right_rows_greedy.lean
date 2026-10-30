-- Prove2me | solution 1 for DerivativeChainContinuation.right_rows_greedy
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:49:24.220536+00:00
-- url     : https://prove2.me/submissions/bb0c6eec-fee2-4593-9148-73711bc07e53

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyReal
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_last_derivative_unique_nearest
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


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators













theorem tower_quadratic_tie (r : RealRows) (hstep : RealRowStep r 0) :
    |rightRow r 1-r 0 0|=|leftRow r 1-r 0 0| := by
  have h := real_step_mean r 0 hstep
  simp only [Nat.cast_zero,zero_add,one_mul] at h
  change (2 : ℝ)*(∑ i : Fin 1,r 0 i)=(∑ i : Fin 2,r 1 i) at h
  rw [Fin.sum_univ_one,Fin.sum_univ_two] at h
  change |r 1 1-r 0 0|=|r 1 0-r 0 0|
  have he : r 1 1-r 0 0=-(r 1 0-r 0 0) := by linarith
  rw [he,abs_neg]


















end DerivativeChainContinuation

theorem solution (r : RealRows) (n : ℕ)
    (hmono : ∀ j≤n,Monotone (r j)) (hstep : ∀ j<n,RealRowStep r j) :
    GreedyRowsTo r n (rightRow r) := by
  refine ⟨fun k hk => ⟨Fin.last k,rfl⟩,?_⟩
  intro k hk i
  cases k with
  | zero =>
    have ht := tower_quadratic_tie r (hstep 0 hk)
    fin_cases i
    · simpa [rightRow,leftRow] using ht.le
    · exact le_rfl
  | succ k =>
    by_cases he : r (k+2) i=rightRow r (k+2)
    · rw [he]
    · exact (last_derivative_unique_nearest k _ _ (hmono _ (by omega))
        (hmono _ (by omega)) (hstep (k+1) hk).1
        (by simpa only [Nat.cast_add,Nat.cast_one,
          (show (k : ℝ)+1+2=(k : ℝ)+3 from by ring)] using (hstep (k+1) hk).2) i he).le
