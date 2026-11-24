-- Prove2me | solution 1 for Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:29:32.872337+00:00
-- url     : https://prove2.me/submissions/92429ae8-e585-4b8f-b081-ab1cf71e004b

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_BranchSandwichDivisors_DivFromPassageAndNorm
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_OperatorNormFibers_PDescentCutA
import Theorems.Thm_Formalism_L2_Geo_ExtensionFiltration_dense_fcoord
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
set_option linter.deprecated false
open Module NumberField
noncomputable section
namespace Formalism.L2.Geo.ExtensionFiltration
private theorem vecAt_apply_linearMap {K V ι W κ : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ] (b : Basis ι K V)
    (b' : Basis κ K W) (φ : V →ₗ[K] W) (v : InfinitePlace K) (f : V) :
    Formalism.HermitianLatticesTheory.vecAt b' v (φ f) = Matrix.mulVec ((LinearMap.toMatrix b b' φ).map v.embedding) (Formalism.HermitianLatticesTheory.vecAt b v f) := by
  funext i
  simp only [Formalism.HermitianLatticesTheory.vecAt]
  rw [← LinearMap.toMatrix_mulVec_repr b b' φ f, RingHom.map_mulVec]
  rfl
end Formalism.L2.Geo.ExtensionFiltration
end
end

set_option autoImplicit false
set_option linter.deprecated false
open Module NumberField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.ExtensionFiltration
namespace Formalism.L2.Geo.ExtensionFiltration
theorem _root_.solution {K V ι W κ : Type} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (hX : ∀ v, IsUnit (X v).det) (φ : V →ₗ[K] W) (v : InfinitePlace K) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f, Formalism.HermitianLatticesTheory.normAt b' X' v (φ f) ≤ C * Formalism.HermitianLatticesTheory.normAt b X v f) :
    Formalism.HN.opNormAt b X b' X' v φ ≤ C := by
  unfold Formalism.HN.opNormAt
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun y => ?_
  have hd := dense_fcoord b X hX v
  refine hd.induction_on (p := fun y => ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v)) y‖ ≤ C * ‖y‖) y ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro f
    have hn : ∀ (κ' : Type) [Fintype κ'] (u : κ' → ℂ), ‖(WithLp.toLp 2 u : EuclideanSpace ℂ κ')‖ = Formalism.HermitianLatticesTheory.cnorm u := by
      intro κ' _ u
      rw [EuclideanSpace.norm_eq]
      rfl
    have hm : Matrix.mulVec ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v) (Formalism.HermitianLatticesTheory.fcoord b X v f) =
        Formalism.HermitianLatticesTheory.fcoord b' X' v (φ f) := by
      simp only [Formalism.HermitianLatticesTheory.fcoord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_right _ _ (hX v)]
      rw [vecAt_apply_linearMap b b' φ v f, Matrix.mulVec_mulVec]
    have h' := h f
    simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_toLp, Matrix.toLin'_apply, hm]
    first
      | exact h'
      | (rw [hn, hn]; exact h')
end Formalism.L2.Geo.ExtensionFiltration
