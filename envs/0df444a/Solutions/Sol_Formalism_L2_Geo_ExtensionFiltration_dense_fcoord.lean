-- Prove2me | solution 1 for Formalism.L2.Geo.ExtensionFiltration.dense_fcoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:17:53.876576+00:00
-- url     : https://prove2.me/submissions/7d552660-f39e-46b6-b160-0c0b0a9ebf04

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_BranchSandwichDivisors_DivFromPassageAndNorm
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_OperatorNormFibers_PDescentCutA
import Theorems.Thm_Formalism_L2_Geo_ExtensionFiltration_dense_emb
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
set_option linter.deprecated false
open Module NumberField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.ExtensionFiltration
namespace Formalism.L2.Geo.ExtensionFiltration
theorem _root_.solution {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    DenseRange fun x : V => (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι) := by
  have h1 : DenseRange (fun f : ι → K => fun i => v.embedding (f i)) :=
    DenseRange.piMap (fun _ => dense_emb v (IsTotallyComplex.isComplex v))
  have h12 : DenseRange (fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x) := by
    have hr : Set.range (fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x) =
        Set.range (fun f : ι → K => fun i => v.embedding (f i)) := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨fun i => b.repr x i, rfl⟩
      · rintro ⟨f, rfl⟩
        refine ⟨b.equivFun.symm f, ?_⟩
        funext i
        have h := congrFun (b.equivFun.apply_symm_apply f) i
        rw [Basis.equivFun_apply] at h
        simp only [Formalism.HermitianLatticesTheory.vecAt, h]
    intro z
    rw [hr]
    exact h1 z
  have hg : Continuous fun u : ι → ℂ => (WithLp.toLp 2 (Matrix.mulVec (X v)⁻¹ u) : EuclideanSpace ℂ ι) := by
    fun_prop
  have hsurj : Function.Surjective fun u : ι → ℂ => (WithLp.toLp 2 (Matrix.mulVec (X v)⁻¹ u) : EuclideanSpace ℂ ι) := by
    intro y
    refine ⟨Matrix.mulVec (X v) (WithLp.ofLp y), ?_⟩
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hX v), Matrix.one_mulVec, WithLp.toLp_ofLp]
  exact hsurj.denseRange.comp h12 hg
end Formalism.L2.Geo.ExtensionFiltration
