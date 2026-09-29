-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_hasStructureConstants_edgeRingConstants_isSpecial_hasHeight_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/fa178cce-7e7f-5eb9-a1ab-cb158110eb27

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
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecial_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasHeight_four_of_hasStructureConstants_edgeRingConstants_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_edgeRingConstants_isSpecial_hasHeight_of_isAlgClosed
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType CerednikDrinfeld.GradedCartierModuleData.module CerednikDrinfeld.GradedCartierModuleData.addCommGroup CerednikDrinfeld.GradedCartierModuleData.instModuleWittVectorSigma CerednikDrinfeld.GradedCartierModuleData.instAddCommGroupSigma"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.FormalODModule.mem_toGradedCartierModuleData_piece_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_homothety_apply CerednikDrinfeld.FormalODModule.mem_gradedSubmodule_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_frobenius_apply CerednikDrinfeld.FormalODModule.varpiLinear_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_varpi_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_verschiebung_apply CerednikDrinfeld.FormalODModule.gradedSubmodule_toAddSubgroup MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k) :
    ∃ (X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (γ : Fin 2 → CartierModule p X.F),
      X.IsHomogeneousVBasis (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) γ ∧
      X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k))) ∧
      X.IsSpecial (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ∧ X.HasHeight 4 := by
  have hpk : ((p : ℕ) : (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0 := by
    have h : (Ideal.Quotient.mk (pIdeal p (WittVector p k))) ((p : ℕ) : WittVector p k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rwa [map_natCast] at h
  haveI : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p := by
    refine CharP.quotient (WittVector p k) p (mem_nonunits_iff.mpr ?_)
    intro hu
    have h0 : (WittVector.constantCoeff : WittVector p k →+* k) ((p : ℕ) : WittVector p k) = 0 := by
      rw [map_natCast, CharP.cast_eq_zero]
    exact (hu.map (WittVector.constantCoeff : WittVector p k →+* k)).ne_zero h0
  have hp0 : ((p : ℕ) : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = 0 := by
    rw [← map_natCast (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))), hpk, map_zero]
  obtain ⟨X, γ, hγ, ha⟩ := CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq p
    (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k))) (EdgeFamily.edgeRingConstants_mul p (WittVector p k ⧸ pIdeal p (WittVector p k)))
  have hsep : IsHausdorff (Ideal.span {((p : ℕ) : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))}) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) := by
    rw [hp0, show Ideal.span {(0 : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))} = ⊥ from by simp]
    infer_instance
  exact ⟨X, γ, hγ, ha, CerednikDrinfeld.FormalODModule.isSpecial_of_isHomogeneousVBasis p _ hsep X γ hγ,
    CerednikDrinfeld.FormalODModule.hasHeight_four_of_hasStructureConstants_edgeRingConstants_of_isAlgClosed p k ι X γ hγ ha⟩

end S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_edgeRingConstants_isSpecial_hasHeight_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_edgeRingConstants_isSpecial_hasHeight_of_isAlgClosed (solution)
