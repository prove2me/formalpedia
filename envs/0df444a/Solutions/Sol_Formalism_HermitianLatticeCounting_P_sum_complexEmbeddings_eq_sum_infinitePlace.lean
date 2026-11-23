-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.sum_complexEmbeddings_eq_sum_infinitePlace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:53.149986+00:00
-- url     : https://prove2.me/submissions/1da62a81-c0ae-453f-81c3-31f5c0ab184a

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SumComplexEmbeddingsEqSumInfinitePlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open NumberField
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {E : Type} [Field E] [NumberField E]
    (hc : ∀ w : InfinitePlace E, w.IsComplex) (F : (E →+* ℂ) → ℂ) :
    ∑ φ : E →+* ℂ, F φ =
      ∑ w : InfinitePlace E, (F w.embedding + F (ComplexEmbedding.conjugate w.embedding)) := by
  classical
  have hfw := Finset.sum_fiberwise Finset.univ (fun φ : E →+* ℂ => InfinitePlace.mk φ) F
  rw [← hfw]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : ComplexEmbedding.conjugate w.embedding ≠ w.embedding := by
    intro h
    exact (InfinitePlace.isComplex_iff.mp (hc w)) (ComplexEmbedding.isReal_iff.mpr h)
  rw [← Finset.sum_pair (f := F) hne.symm]
  congr 1
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro rfl
    rcases InfinitePlace.embedding_mk_eq φ with h | h
    · exact Or.inl h.symm
    · right
      rw [h]
      exact (star_star φ).symm
  · rintro (rfl | rfl)
    · exact InfinitePlace.mk_embedding w
    · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
end Formalism.HermitianLatticeCounting.P
