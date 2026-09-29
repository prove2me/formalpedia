-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.hasHeight_four_of_hasStructureConstants_edgeRingConstants_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/aa21fde9-3875-5f6f-a2ad-da0027888a79

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_X_pow_mem_of_forall_finrank_eq_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_finrank_kerAlgebra_map_act_eq_pow_four_of_hasStructureConstants_edgeRingConstants_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_act_of_hasStructureConstants_edgeConstants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_hasHeight_four_of_hasStructureConstants_edgeRingConstants_of_isAlgClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType CerednikDrinfeld.GradedCartierModuleData.module CerednikDrinfeld.GradedCartierModuleData.addCommGroup CerednikDrinfeld.GradedCartierModuleData.instModuleWittVectorSigma CerednikDrinfeld.GradedCartierModuleData.instAddCommGroupSigma MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "CerednikDrinfeld.FormalODModule.mem_toGradedCartierModuleData_piece_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_homothety_apply CerednikDrinfeld.FormalODModule.mem_gradedSubmodule_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_frobenius_apply CerednikDrinfeld.FormalODModule.varpiLinear_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_varpi_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_verschiebung_apply CerednikDrinfeld.FormalODModule.gradedSubmodule_toAddSubgroup MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq"
p2m_attr_erase "simp" "MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (γ : Fin 2 → CartierModule p X.F)
    (hγ : X.IsHomogeneousVBasis (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) γ)
    (ha : X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k)))) :
    X.HasHeight 4 := by
  classical

  have hmax : (pIdeal p (WittVector p k)).IsMaximal := by
    have h := (WittVector.irreducible p (k := k)).maximalIdeal_eq
    rw [pIdeal, ← h]
    exact IsLocalRing.maximalIdeal.isMaximal (WittVector p k)
  letI hF : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) :=
    @Ideal.Quotient.field _ _ (pIdeal p (WittVector p k)) hmax

  haveI : IsNoetherianRing (FormalOmega.edgeQuot (WittVector p k ⧸ pIdeal p (WittVector p k))
      (0 : WittVector p k ⧸ pIdeal p (WittVector p k))) := by
    unfold FormalOmega.edgeQuot
    infer_instance
  haveI hNoeth : IsNoetherianRing (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) :=
    inferInstance

  have hp1 : 1 ≤ p - 1 := by
    have := (Fact.out : p.Prime).two_le
    omega
  let x0 : (FormalOmega.chartE (WittVector p k ⧸ pIdeal p (WittVector p k))
      (0 : WittVector p k ⧸ pIdeal p (WittVector p k)) p).obj (WittVector p k ⧸ pIdeal p (WittVector p k)) :=
    ⟨((0 : WittVector p k ⧸ pIdeal p (WittVector p k)), 0), by
      refine ⟨by simp, ?_, ?_⟩ <;>
      · rw [zero_pow (by omega), zero_sub]
        exact isUnit_one.neg⟩
  haveI : Nontrivial (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) :=
    (FormalOmega.chartERing.lift x0).toRingHom.domain_nontrivial

  have hpk : ((p : ℕ) : (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0 := by
    have h : (Ideal.Quotient.mk (pIdeal p (WittVector p k))) ((p : ℕ) : WittVector p k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rwa [map_natCast] at h
  have hp0 : ((p : ℕ) : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = 0 := by
    rw [← map_natCast (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))), hpk, map_zero]
  haveI : CharP (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp0

  unfold FormalODModule.HasHeight
  refine CerednikDrinfeld.FormalODModule.hasKernelOfDegree_of_X_pow_mem_of_forall_finrank_eq_of_isAlgClosed
    (X.act (p : Zp2 p)) (X.isLawHom_act (p : Zp2 p)).1 ?_ (p ^ 4) ?_
  · exact CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_act_of_hasStructureConstants_edgeConstants p
      (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))
      (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))
      (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))
      (EdgeFamily.edgeRingCharP.ξ_mul_η p (WittVector p k ⧸ pIdeal p (WittVector p k))) X γ hγ ha
  · intro κ _ _ f
    exact CerednikDrinfeld.FormalODModule.finrank_kerAlgebra_map_act_eq_pow_four_of_hasStructureConstants_edgeRingConstants_of_isAlgClosed
      p k ι X γ hγ ha κ f

end S_CerednikDrinfeld_FormalODModule_hasHeight_four_of_hasStructureConstants_edgeRingConstants_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_hasHeight_four_of_hasStructureConstants_edgeRingConstants_of_isAlgClosed (solution)
