-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.trace_eq_sum_infinitePlace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:36.444808+00:00
-- url     : https://prove2.me/submissions/d48d6b63-c637-4a43-8610-c5294fd41915

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SumComplexEmbeddingsEqSumInfinitePlace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sum_complexEmbeddings_eq_sum_infinitePlace

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
    (hc : ∀ w : InfinitePlace E, w.IsComplex) (a : E) :
    ((Algebra.trace ℚ E a : ℚ) : ℝ) = ∑ w : InfinitePlace E, 2 * (w.embedding a).re := by
  have h : algebraMap ℚ ℂ (Algebra.trace ℚ E a) = ∑ σ : E →ₐ[ℚ] ℂ, σ a := by
    exact trace_eq_sum_embeddings ℂ

  rw [eq_ratCast] at h
  have h1 : ((Algebra.trace ℚ E a : ℚ) : ℂ) = ∑ φ : E →+* ℂ, φ a := by
    rw [h]
    exact (Equiv.sum_comp (RingHom.equivRatAlgHom E ℂ) (fun σ : E →ₐ[ℚ] ℂ => σ a)).symm
  calc ((Algebra.trace ℚ E a : ℚ) : ℝ) = (((Algebra.trace ℚ E a : ℚ) : ℂ)).re := by simp
    _ = (∑ φ : E →+* ℂ, φ a).re := by rw [h1]
    _ = (∑ w : InfinitePlace E,
          (w.embedding a + ComplexEmbedding.conjugate w.embedding a)).re := by
        rw [sum_complexEmbeddings_eq_sum_infinitePlace hc (fun φ => φ a)]
    _ = ∑ w : InfinitePlace E, 2 * (w.embedding a).re := by
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp [ComplexEmbedding.conjugate_coe_eq, two_mul]
end Formalism.HermitianLatticeCounting.P
