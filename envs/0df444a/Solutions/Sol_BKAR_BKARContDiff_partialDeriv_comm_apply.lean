-- Prove2me | solution 1 for BKAR.BKARContDiff.partialDeriv_comm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:41.519949+00:00
-- url     : https://prove2.me/submissions/c86f2a0e-4ac3-494f-a122-b8e37b108315

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_Smoothness
import Definitions.Def_BKAR_PartialDerivSymmetry
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_edgeBasis_self
import Theorems.Thm_BKAR_mixedPartialList_cons
import Theorems.Thm_BKAR_mixedPartialList_cons_apply
import Theorems.Thm_BKAR_mixedPartialList_nil
import Theorems.Thm_BKAR_mixedPartialList_nil_apply
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_cons
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_nil
import Theorems.Thm_BKAR_orderedSimplexIntegral_cons
import Theorems.Thm_BKAR_orderedSimplexIntegral_nil
import Theorems.Thm_BKAR_orderedSimplexParams_cons
import Theorems.Thm_BKAR_orderedSimplexParams_nil
import Theorems.Thm_BKAR_partialDeriv_of_hasFDerivAt
import Theorems.Thm_BKAR_updateCoord_same_value
import Theorems.Thm_BKAR_updateCoord_self
import Theorems.Thm_BKAR_updateCoord_update_same
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegralAux_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegral_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegrand_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.derivativeOrder_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_cons
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_nil
attribute [local simp] BKAR.Forest.emptyActiveEdge_val
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.edgeBasis_self
attribute [local simp] BKAR.mixedPartialList_cons
attribute [local simp] BKAR.mixedPartialList_cons_apply
attribute [local simp] BKAR.mixedPartialList_nil
attribute [local simp] BKAR.mixedPartialList_nil_apply
attribute [local simp] BKAR.orderedSimplexIntegralAux_cons
attribute [local simp] BKAR.orderedSimplexIntegralAux_nil
attribute [local simp] BKAR.orderedSimplexIntegral_cons
attribute [local simp] BKAR.orderedSimplexIntegral_nil
attribute [local simp] BKAR.orderedSimplexParams_cons
attribute [local simp] BKAR.orderedSimplexParams_nil
attribute [local simp] BKAR.updateCoord_same_value
attribute [local simp] BKAR.updateCoord_self
attribute [local simp] BKAR.updateCoord_update_same



set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.BKARContDiff
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.BKARContDiff
theorem _root_.solution
    (hρ : BKARContDiff ρ) (e f : Edge V) (x : Edge V → ℝ) :
    BKAR.partialDeriv e (BKAR.partialDeriv f ρ) x =
      BKAR.partialDeriv f (BKAR.partialDeriv e ρ) x := by
  have hpf :
      BKAR.partialDeriv f ρ =
        fun y : Edge V → ℝ =>
          (fderiv ℝ ρ y : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis f) := by
    funext y
    exact partialDeriv_of_hasFDerivAt f
      ((hρ.differentiableAt y).hasFDerivAt)
  have hpe :
      BKAR.partialDeriv e ρ =
        fun y : Edge V → ℝ =>
          (fderiv ℝ ρ y : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis e) := by
    funext y
    exact partialDeriv_of_hasFDerivAt e
      ((hρ.differentiableAt y).hasFDerivAt)
  have hdiffF :
      DifferentiableAt ℝ (BKAR.partialDeriv f ρ) x :=
    ((hρ.partialDeriv f).differentiableAt x)
  have hdiffE :
      DifferentiableAt ℝ (BKAR.partialDeriv e ρ) x :=
    ((hρ.partialDeriv e).differentiableAt x)
  have hc :
      DifferentiableAt ℝ
        (fun y : Edge V → ℝ =>
          (fderiv ℝ ρ y : (Edge V → ℝ) →L[ℝ] ℝ)) x :=
    (hρ.fderiv_contDiff.differentiable (by simp)).differentiableAt
  have hconstF :
      DifferentiableAt ℝ (fun _ : Edge V → ℝ => edgeBasis f) x :=
    differentiableAt_const _
  have hconstE :
      DifferentiableAt ℝ (fun _ : Edge V → ℝ => edgeBasis e) x :=
    differentiableAt_const _
  have hclmF :=
    fderiv_clm_apply
      (𝕜 := ℝ)
      (c := fun y : Edge V → ℝ =>
        (fderiv ℝ ρ y : (Edge V → ℝ) →L[ℝ] ℝ))
      (u := fun _ : Edge V → ℝ => edgeBasis f)
      (x := x) hc hconstF
  have hclmE :=
    fderiv_clm_apply
      (𝕜 := ℝ)
      (c := fun y : Edge V → ℝ =>
        (fderiv ℝ ρ y : (Edge V → ℝ) →L[ℝ] ℝ))
      (u := fun _ : Edge V → ℝ => edgeBasis e)
      (x := x) hc hconstE
  have hleft :
      fderiv ℝ (BKAR.partialDeriv f ρ) x (edgeBasis e) =
        (fderiv ℝ (fderiv ℝ ρ) x
          (edgeBasis e) : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis f) := by
    rw [hpf, hclmF]
    simp [fderiv_fun_const]
  have hright :
      fderiv ℝ (BKAR.partialDeriv e ρ) x (edgeBasis f) =
        (fderiv ℝ (fderiv ℝ ρ) x
          (edgeBasis f) : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis e) := by
    rw [hpe, hclmE]
    simp [fderiv_fun_const]
  have hsymm :
      (fderiv ℝ (fderiv ℝ ρ) x
          (edgeBasis e) : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis f) =
        (fderiv ℝ (fderiv ℝ ρ) x
          (edgeBasis f) : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis e) := by
    exact
      ((hρ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt
        (n := (∞ : WithTop ℕ∞))
        (by simp only [minSmoothness_of_isRCLikeNormedField]
            exact WithTop.coe_le_coe.mpr le_top)).eq
          (edgeBasis e) (edgeBasis f)
  calc
    BKAR.partialDeriv e (BKAR.partialDeriv f ρ) x
        = fderiv ℝ (BKAR.partialDeriv f ρ) x (edgeBasis e) := by
          exact partialDeriv_of_hasFDerivAt e hdiffF.hasFDerivAt
    _ = (fderiv ℝ (fderiv ℝ ρ) x
          (edgeBasis e) : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis f) := hleft
    _ = (fderiv ℝ (fderiv ℝ ρ) x
          (edgeBasis f) : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis e) := hsymm
    _ = fderiv ℝ (BKAR.partialDeriv e ρ) x (edgeBasis f) := hright.symm
    _ = BKAR.partialDeriv f (BKAR.partialDeriv e ρ) x := by
          exact (partialDeriv_of_hasFDerivAt f hdiffE.hasFDerivAt).symm
end BKAR.BKARContDiff
