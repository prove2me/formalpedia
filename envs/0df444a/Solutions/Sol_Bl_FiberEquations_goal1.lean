-- Prove2me | solution 1 for Bl.FiberEquations.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:06.563091+00:00
-- url     : https://prove2.me/submissions/6bec2b82-869a-4619-83b9-bffe451dcdea

import Mathlib
import Definitions.Def_Lemmata_FiberEquations_FiberEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset NumberField Module
open scoped ComplexConjugate nonZeroDivisors
namespace Bl.FiberEquations
private lemma fiber_eq {E : Type} [Field E] (w : InfinitePlace E) [DecidableEq (InfinitePlace E)]
    [DecidableEq (E →+* ℂ)] [Fintype (E →+* ℂ)] :
    ({φ | InfinitePlace.mk φ = w} : Finset (E →+* ℂ)) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  conv_lhs => rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [← h, ComplexEmbedding.involutive_conjugate E φ]
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h, ComplexEmbedding.involutive_conjugate E]
end Bl.FiberEquations
end

set_option autoImplicit false
open Finset NumberField Module
open scoped ComplexConjugate nonZeroDivisors
open Bl Bl.FiberEquations
namespace Bl.FiberEquations
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ w : InfinitePlace E, 2 * (w.embedding x).re := by
  classical
  have h1 : ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ φ : E →+* ℂ, φ x := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := x)
    rw [eq_ratCast] at h
    rw [h]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ (fun σ => rfl)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, h1, Complex.ofReal_sum,
    ← Finset.sum_fiberwise univ (fun φ : E →+* ℂ => InfinitePlace.mk φ) (fun φ => φ x)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro h
    exact IsTotallyComplex.complexEmbedding_not_isReal w.embedding
      (ComplexEmbedding.isReal_iff.mpr h.symm)
  rw [fiber_eq w, Finset.sum_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
end Bl.FiberEquations
