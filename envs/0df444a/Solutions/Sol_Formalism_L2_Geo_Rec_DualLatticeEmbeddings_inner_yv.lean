-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.DualLatticeEmbeddings.inner_yv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:14:43.489683+00:00
-- url     : https://prove2.me/submissions/442ae559-f5d7-4ff6-a858-3c405965c1d6

import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_SumUliftFinsetFinTwoExpand
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_inner_mkE
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_realize_eq
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_inner_mkE_fc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
variable [StarRing K]
variable [IsTotallyComplex K]
private theorem trace_re_lemma (a : K) :
    ((Algebra.trace ℚ K a : ℚ) : ℝ) = ∑ v : InfinitePlace K, 2 * (v.embedding a).re := by
  classical
  have h1 : ((Algebra.trace ℚ K a : ℚ) : ℂ) = ∑ σ : K →+* ℂ, σ a := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := K) (E := ℂ) (x := a)
    rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ : K →+* ℂ => σ a)
      (fun τ : K →ₐ[ℚ] ℂ => τ a) (fun σ => rfl)]
    simpa using h
  have h2 : ∑ σ : K →+* ℂ, σ a = ∑ v : InfinitePlace K, (((2 * (v.embedding a).re : ℝ)) : ℂ) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun σ => InfinitePlace.mk σ)]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hne : NumberField.ComplexEmbedding.conjugate v.embedding ≠ v.embedding := by
      intro h
      have hr : v.IsReal :=
        InfinitePlace.isReal_iff.mpr (NumberField.ComplexEmbedding.isReal_iff.mpr h)
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr (NumberField.IsTotallyComplex.isComplex v)) hr
    have hset : Finset.univ.filter (fun σ => InfinitePlace.mk σ = v) =
        {v.embedding, NumberField.ComplexEmbedding.conjugate v.embedding} := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro h
        rw [← InfinitePlace.mk_embedding v, InfinitePlace.mk_eq_iff] at h
        rcases h with h | h
        · exact Or.inl h
        · right
          rw [← h]
          ext x
          simp [NumberField.ComplexEmbedding.conjugate_coe_eq]
      · rintro (h | h)
        · rw [h]
          exact InfinitePlace.mk_embedding v
        · rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
    rw [hset, Finset.sum_pair hne.symm, NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, h1, h2, Complex.ofReal_sum]
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
variable [StarRing K]
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ} [StarRing K] [IsTotallyComplex K]
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
end
end
end
end

set_option autoImplicit false
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
variable [StarRing K]
variable [IsTotallyComplex K]
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
theorem _root_.solution (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hXf : ∀ v, IsUnit (Xf v).det)
    (x ξ : Fin n → K) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf x) (yv Xf ξ) =
      ((Algebra.trace ℚ K (∑ i, ξ i * x i) : ℚ) : ℝ) := by
  rw [realize_eq]
  unfold yv
  rw [inner_mkE, trace_re_lemma]
  exact Finset.sum_congr rfl fun v _ => inner_mkE_fc Xf hXf x ξ v
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
