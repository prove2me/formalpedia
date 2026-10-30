-- Prove2me | solution 1 for DerivativeChainContinuation.positive_actual_low_row_root_zero
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:00:38.645804+00:00
-- url     : https://prove2.me/submissions/7527c3be-d5c4-4786-9b4d-dba7f9ff6502

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_actual_row_class
import Theorems.Thm_DerivativeChainContinuation_positive_spoke_low_degree_root_zero
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
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem actual_complex_source_natDegree {n : ℕ} (a : Fin (n+1) → ℂ) :
    (fromRoots a).natDegree=n+1 := by
  simp only [fromRoots]
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]
  simp

theorem actual_complex_row_natDegree {n : ℕ} (a : Fin (n+1) → ℂ)
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n+1) : (row a m).natDegree=m := by
  rw [row,complex_iterate_derivative_natDegree,actual_complex_source_natDegree]
  omega






















end DerivativeChainContinuation

theorem solution {n : ℕ} (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hp : fromRoots a=spokePoly k r Q) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n+1)
    (hmlow : m<k) (z : ℂ) (hroot : (row a m).eval z=0) : z=0 := by
  obtain ⟨s,V,hV,heq⟩ := positive_actual_row_class a k r Q hk hQ hp m hm hmn
  have hdeg : (spokePoly k s V).natDegree<k := by
    rw [←heq,actual_complex_row_natDegree a m hm hmn]
    exact hmlow
  exact positive_spoke_low_degree_root_zero k s V hk hV hdeg z (by rwa [←heq])
