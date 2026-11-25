-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NormUnitsOrthogonality.gram_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:14:30.901799+00:00
-- url     : https://prove2.me/submissions/7fcaf14b-fdc7-4990-b351-98f6d7b73b9e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LinIndOrth
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFSubspace
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DetUnitOfSelfdual
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_form_repr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NormUnitsOrthogonality
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases
  Formalism.L2.SG.Pf.UnitPairSolutions
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
namespace Formalism.L2.SG.Pf.NormUnitsOrthogonality
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (β γ : Basis κ K V) :
    gramK h γ = (β.toMatrix γ)ᴴ * gramK h β * β.toMatrix γ := by
  ext i j
  have e : gramK h γ i j = h (γ i) (γ j) := rfl
  rw [e, form_repr h β, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Basis.toMatrix_apply, Basis.equivFun_apply, Pi.star_apply]
end Formalism.L2.SG.Pf.NormUnitsOrthogonality
