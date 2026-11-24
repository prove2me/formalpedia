-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:55.909008+00:00
-- url     : https://prove2.me/submissions/4a6ce2ba-ab0f-45c4-8549-e0b686e9b3a1

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (a : K) :
    ((Algebra.trace ℚ K a : ℚ) : ℝ) = 2 * ∑ v : InfinitePlace K, (v.embedding a).re := by
  have h1 : ((Algebra.trace ℚ K a : ℚ) : ℂ) = ∑ φ : K →+* ℂ, φ a := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ)]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ a) (fun σ => σ a)
      fun _ => rfl).symm
  have hre : ((Algebra.trace ℚ K a : ℚ) : ℝ) = ∑ φ : K →+* ℂ, (φ a).re := by
    rw [← Complex.re_sum, ← h1, Complex.ratCast_re]
  classical
  rw [hre, ← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => (φ a).re),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => (w.embedding a).re) ?_, Finset.sum_const, nsmul_eq_mul]
  · congr 1
    norm_cast
    convert InfinitePlace.card_filter_mk_eq w
    rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2
      (IsTotallyComplex.isComplex w))]
  · intro φ hφ
    have hw : InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
      rw [(Finset.mem_filter.1 hφ).2, InfinitePlace.mk_embedding]
    rcases InfinitePlace.mk_eq_iff.1 hw with h | h
    · rw [h]
    · rw [← h, NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
end Formalism.HermitianLatticesTheory
