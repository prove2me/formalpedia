-- Prove2me | solution 1 for D1Bound5.lagrange_power_moment_eq_homogeneousMultisetSum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:54.629481+00:00
-- url     : https://prove2.me/submissions/508c7ff8-b36b-41b0-8fb8-c768bb4bc6e5

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions
import Theorems.Thm_D1Bound5_homogeneousMultisetSum_insert
import Theorems.Thm_D1Bound5_homogeneousMultisetSum_singleton
import Theorems.Thm_D1Bound5_homogeneousMultisetSum_zero
import Theorems.Thm_D1Bound5_lagrange_power_moment_insert

section
open Polynomial Finset

namespace D1Bound5







/-- Every higher Lagrange power moment is the complete homogeneous
multiset sum, for every nonempty finite set of distinct nodes. -/
theorem _root_.solution
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (hs : s.Nonempty)
    (hinj : Set.InjOn a s) (k : ℕ) :
    (∑ i ∈ s, (a i) ^ (s.card - 1 + k) /
      (∏ j ∈ s.erase i, (a i - a j))) =
      homogeneousMultisetSum (fun i : s => a i) k := by
  revert hs hinj
  induction s using Finset.induction_on generalizing k with
  | empty =>
      intro hs
      simp at hs
  | @insert t s ht ih =>
      intro hs hinj
      obtain rfl | hs' := s.eq_empty_or_nonempty
      · simp only [Finset.insert_empty, Finset.card_singleton, Nat.sub_self,
          zero_add, Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty, div_one]
        exact (homogeneousMultisetSum_singleton a t k).symm
      have hsinj : Set.InjOn a s := hinj.mono (by intro i hi; exact Finset.mem_insert_of_mem hi)
      have hsep : ∀ i ∈ s, a i ≠ a t := by
        intro i hi heq
        have hit := hinj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self t s) heq
        exact ht (hit ▸ hi)
      have hp : 0 < s.card := hs'.card_pos
      induction k with
      | zero =>
          have hn : (insert t s).card - 1 < (insert t s).card := by
            rw [Finset.card_insert_of_notMem ht]
            omega
          have hdegree : ((X : F[X]) ^ ((insert t s).card - 1)).degree <
              ((insert t s).card : WithBot ℕ) := by
            rw [Polynomial.degree_X_pow]
            exact_mod_cast hn
          have h := Lagrange.coeff_eq_sum (s := insert t s) (v := a)
            (P := (X : F[X]) ^ ((insert t s).card - 1)) hinj hdegree
          simpa [Polynomial.eval_pow, Polynomial.coeff_X_pow] using h.symm
      | succ k hk =>
          have hold := ih (k + 1) hs' hsinj
          have hold' : (∑ i ∈ s, (a i) ^ (s.card + k) /
              (∏ j ∈ s.erase i, (a i - a j))) =
              homogeneousMultisetSum (fun i : s => a i) (k + 1) := by
            simpa only [show s.card - 1 + (k + 1) = s.card + k by omega] using hold
          have hnew' : (∑ i ∈ insert t s, (a i) ^ (s.card + k) /
              (∏ j ∈ (insert t s).erase i, (a i - a j))) =
              homogeneousMultisetSum (fun i : (insert t s : Finset ι) => a i) k := by
            simpa [Finset.card_insert_of_notMem ht] using hk
          have h := lagrange_power_moment_insert s a t ht hsep (s.card + k)
          rw [hnew', hold', ← homogeneousMultisetSum_insert s a t ht k] at h
          simpa [Finset.card_insert_of_notMem ht, Nat.add_assoc] using h



end D1Bound5
end
