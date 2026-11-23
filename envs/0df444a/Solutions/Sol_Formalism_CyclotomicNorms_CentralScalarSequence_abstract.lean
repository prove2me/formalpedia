-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.abstract
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:25.538802+00:00
-- url     : https://prove2.me/submissions/b2463673-e8dd-4905-8901-860eed4f5113

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.CentralScalarSequence
variable {G : Type} [Group G]
namespace Formalism.CyclotomicNorms.CentralScalarSequence
theorem _root_.solution {W : Type} [AddCommGroup W] (T S : ℕ → ℕ → W)
    (h1 : ∀ M j, j < M → T (M + 1) j = - S M j) (h2 : ∀ M, T (M + 1) M = - T M M)
    (h3 : ∀ M i, i ≤ M → T i (M + 1) = - S i M) (N : ℕ) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), T i j) +
      (∑ i ∈ range N, ∑ j ∈ range N, S i j) = T N N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have eT : ∑ i ∈ range (N + 1 + 1), ∑ j ∈ range (N + 1 + 1), T i j =
        (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), T i j) + (∑ i ∈ range (N + 1), T i (N + 1))
        + ((∑ j ∈ range N, T (N + 1) j) + T (N + 1) N) + T (N + 1) (N + 1) := by
      rw [sum_range_succ _ (N + 1)]
      simp only [sum_range_succ _ (N + 1), sum_add_distrib]
      rw [← sum_range_succ (fun j => T (N + 1) j) N]
      abel
    have eS : ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), S i j =
        (∑ i ∈ range N, ∑ j ∈ range N, S i j) + (∑ i ∈ range N, S i N) +
        (∑ j ∈ range N, S N j) + S N N := by
      rw [sum_range_succ _ N]
      simp only [sum_range_succ _ N, sum_add_distrib]
      abel
    have e1 : ∑ j ∈ range N, T (N + 1) j = - ∑ j ∈ range N, S N j := by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun j hj => h1 N j (mem_range.mp hj)
    have e2 : ∑ i ∈ range (N + 1), T i (N + 1) = - ((∑ i ∈ range N, S i N) + S N N) := by
      rw [← sum_range_succ (fun i => S i N) N, ← sum_neg_distrib]
      exact sum_congr rfl fun i hi => h3 N i (Nat.lt_succ_iff.mp (mem_range.mp hi))
    rw [eT, eS, e1, e2, h2 N]
    have ih' := eq_sub_of_add_eq ih
    rw [ih']
    abel
end Formalism.CyclotomicNorms.CentralScalarSequence
