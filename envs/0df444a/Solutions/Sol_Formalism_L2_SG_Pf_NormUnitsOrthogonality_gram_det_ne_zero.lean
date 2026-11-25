-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NormUnitsOrthogonality.gram_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:56:39.249394+00:00
-- url     : https://prove2.me/submissions/20f501a0-728f-4612-a289-d7b32c9baf1b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LinIndOrth
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFSubspace
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DetUnitOfSelfdual
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_form_repr
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq
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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h) (β : Basis κ K V) :
    (gramK h β).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  have hy : ∀ x, h x (β.equivFun.symm v) = 0 := by
    intro x
    rw [form_repr h β, LinearEquiv.apply_symm_apply, hGv]
    simp
  have h0 : β.equivFun.symm v = 0 := by
    apply hnd
    intro y
    have := hs.eq y (β.equivFun.symm v)
    rw [← this, hy y, map_zero]
  exact β.equivFun.symm.injective (by rw [h0, map_zero])
end Formalism.L2.SG.Pf.NormUnitsOrthogonality
