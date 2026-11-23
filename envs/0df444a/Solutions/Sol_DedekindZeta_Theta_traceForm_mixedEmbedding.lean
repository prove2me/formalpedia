-- Prove2me | solution 1 for DedekindZeta.Theta.traceForm_mixedEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:12:12.90418+00:00
-- url     : https://prove2.me/submissions/fc50faa1-5b26-4cbb-814e-08d311bf2a25

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_sum_embeddings_mul

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (b a : K) :
    traceForm K (mixedEmbedding K b) a
      = algebraMap ℚ ℝ (Algebra.trace ℚ K (b * a)) := by
  classical
  -- The `mk`-fiber over a place `w` is the conjugate pair (singleton when real).
  have hfib : ∀ w : InfinitePlace K,
      (Finset.univ.filter fun σ : K →+* ℂ => InfinitePlace.mk σ = w)
        = {InfinitePlace.embedding w,
            ComplexEmbedding.conjugate (InfinitePlace.embedding w)} := by
    intro w
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      rcases InfinitePlace.mk_eq_iff.mp (h.trans (InfinitePlace.mk_embedding w).symm) with
        h1 | h1
      · exact Or.inl h1
      · exact Or.inr ((ComplexEmbedding.involutive_conjugate K).eq_iff.mp h1)
    · rintro (h1 | h1)
      · rw [h1, InfinitePlace.mk_embedding]
      · rw [h1, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  have hReal : ∀ w : {w : InfinitePlace K // w.IsReal},
      (∑ σ ∈ Finset.univ.filter fun σ : K →+* ℂ =>
            InfinitePlace.mk σ = (w : InfinitePlace K),
          (σ b * σ a).re)
        = (mixedEmbedding K b).1 w * (mixedEmbedding K a).1 w := by
    intro w
    rw [hfib w.1, InfinitePlace.conjugate_embedding_eq_of_isReal w.2,
      Finset.insert_eq_self.mpr (Finset.mem_singleton_self _), Finset.sum_singleton,
      mixedEmbedding_apply_isReal, mixedEmbedding_apply_isReal,
      ← InfinitePlace.embedding_of_isReal_apply w.2 b,
      ← InfinitePlace.embedding_of_isReal_apply w.2 a,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hCplx : ∀ w : {w : InfinitePlace K // w.IsComplex},
      (∑ σ ∈ Finset.univ.filter fun σ : K →+* ℂ =>
            InfinitePlace.mk σ = (w : InfinitePlace K),
          (σ b * σ a).re)
        = 2 * ((mixedEmbedding K b).2 w * (mixedEmbedding K a).2 w).re := by
    intro w
    have hne : InfinitePlace.embedding (w : InfinitePlace K)
        ≠ ComplexEmbedding.conjugate (InfinitePlace.embedding (w : InfinitePlace K)) := by
      intro h
      refine (InfinitePlace.not_isReal_iff_isComplex.mpr w.2) ?_
      rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
      exact h.symm
    rw [hfib w.1, Finset.sum_pair hne, mixedEmbedding_apply_isComplex,
      mixedEmbedding_apply_isComplex, ComplexEmbedding.conjugate_coe_eq,
      ComplexEmbedding.conjugate_coe_eq]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hsum : traceForm K (mixedEmbedding K b) a = (∑ σ : K →+* ℂ, σ b * σ a).re := by
    rw [traceForm, Complex.re_sum,
      ← Finset.sum_fiberwise Finset.univ (fun σ : K →+* ℂ => InfinitePlace.mk σ)
        (fun σ : K →+* ℂ => (σ b * σ a).re),
      InfinitePlace.sum_eq_sum_add_sum]
    rw [Finset.sum_congr rfl (fun w _ => hReal w),
      show (∑ w : {w : InfinitePlace K // w.IsComplex},
            ∑ σ ∈ Finset.univ.filter fun σ : K →+* ℂ =>
              InfinitePlace.mk σ = (w : InfinitePlace K),
            (σ b * σ a).re)
          = 2 * ∑ w : {w : InfinitePlace K // w.IsComplex},
              ((mixedEmbedding K b).2 w * (mixedEmbedding K a).2 w).re
        from by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun w _ => hCplx w)]
  rw [hsum, sum_embeddings_mul, IsScalarTower.algebraMap_apply ℚ ℝ ℂ,
    Complex.coe_algebraMap, Complex.ofReal_re]
end DedekindZeta.Theta
