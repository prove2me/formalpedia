-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData_wittVector_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/bfa65ccc-e644-55da-bf80-70538a235c47

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_of_free
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData_wittVector_quotient
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

open scoped PadicInt

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1)) :
    (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsSpecialCartierModule := by
  classical

  have hmax : (pIdeal p (WittVector p k)).IsMaximal := by
    have h := (WittVector.irreducible p (k := k)).maximalIdeal_eq
    rw [pIdeal, ← h]
    exact IsLocalRing.maximalIdeal.isMaximal (WittVector p k)
  have hnu : ((p : ℕ) : WittVector p k) ∈ nonunits (WittVector p k) := fun hu =>
    hmax.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_singleton _)) hu)
  haveI : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p := CharP.quotient (WittVector p k) p hnu
  letI hF : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := @Ideal.Quotient.field _ _ (pIdeal p (WittVector p k)) hmax
  have h₀ : Module.Free (WittVector p k ⧸ pIdeal p (WittVector p k)) ↥(Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) := Module.Free.of_divisionRing _ _
  have h₁ : Module.Free (WittVector p k ⧸ pIdeal p (WittVector p k)) ↥(Φ.lieOne ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) := Module.Free.of_divisionRing _ _
  obtain ⟨γ, hγ⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_of_free p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) Φ hΦ h₀ h₁
  exact (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) Φ γ hγ hcΦ).2

end S_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData_wittVector_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData_wittVector_quotient (solution)
