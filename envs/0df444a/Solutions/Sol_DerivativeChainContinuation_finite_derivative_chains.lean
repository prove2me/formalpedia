-- Prove2me | solution 1 for DerivativeChainContinuation.finite_derivative_chains
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:50:44.254401+00:00
-- url     : https://prove2.me/submissions/29007ecf-a45f-4025-89ec-c440d7181533

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


theorem solution {n : ℕ} (a : Fin (n+1) → ℂ) :
    {z : Fin (n+1) → ℂ | IsChain a z}.Finite := by
  have hdeg : (fromRoots a).natDegree=n+1 := by
    unfold fromRoots
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]
    simp
  have hd (k : ℕ) : (derivative^[k] (fromRoots a)).natDegree=n+1-k := by
    induction k with
    | zero => exact hdeg
    | succ k ih =>
      rw [Function.iterate_succ_apply',natDegree_derivative,ih]
      omega
  have hne (i : Fin (n+1)) : row a (i.val+1)≠0 := by
    intro he
    have h := hd (n+1-(i.val+1))
    change (row a (i.val+1)).natDegree=n+1-(n+1-(i.val+1)) at h
    rw [he,natDegree_zero] at h
    omega
  have hfinite := Set.Finite.pi' (fun i : Fin (n+1) =>
    Polynomial.finite_setOfPred_isRoot (hne i))
  simpa only [DerivativeChainPrivate.IsChain,Polynomial.IsRoot,Set.mem_ofPred_eq] using hfinite
