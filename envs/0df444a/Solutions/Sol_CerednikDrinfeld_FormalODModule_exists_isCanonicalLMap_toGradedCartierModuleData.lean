-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7c600c1d-d0fd-50af-8847-ad5bc8350020

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_liftRing_isHomogeneousVBasis_hasStructureConstants_liftConstants_and_isIso_of_isHausdorff
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_Hom_bijective_map_and_forall_map_eq_of_isIso
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsBaseChangeAlong_comp_of_bijective
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.FormalODModule CerednikDrinfeld.CartierLift MvFormalGroup.CartierModule

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hsep : IsHausdorff (Ideal.span {(p : B)}) B)
    (X : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) :
    ∃ L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod,
      (X.toGradedCartierModuleData j hc).IsCanonicalLMap L := by
  classical
  obtain ⟨a, ha, h01⟩ := CerednikDrinfeld.FormalODModule.exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis p j X γ hγ
  obtain ⟨Xl, γl, hγl, hal, u, hu, hγu⟩ := CerednikDrinfeld.FormalODModule.exists_liftRing_isHomogeneousVBasis_hasStructureConstants_liftConstants_and_isIso_of_isHausdorff p j hsep X γ hγ a ha h01
  have hcU : IsCompl (Xl.gradedPiece (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1))) 0) (Xl.gradedPiece (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1))) 1) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis p (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1))) Xl γl hγl
  have hγb := hγl.map (CartierLift.liftHom j (a 0 0) (a 0 1) h01)
  have hcB : IsCompl ((Xl.map (CartierLift.liftHom j (a 0 0) (a 0 1) h01)).gradedPiece ((CartierLift.liftHom j (a 0 0) (a 0 1) h01).comp (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1)))) 0)
      ((Xl.map (CartierLift.liftHom j (a 0 0) (a 0 1) h01)).gradedPiece ((CartierLift.liftHom j (a 0 0) (a 0 1) h01).comp (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1)))) 1) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis p ((CartierLift.liftHom j (a 0 0) (a 0 1) h01).comp (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1)))) (Xl.map (CartierLift.liftHom j (a 0 0) (a 0 1) h01)) _ hγb
  suffices H : ∀ hc' : IsCompl (X.gradedPiece ((CartierLift.liftHom j (a 0 0) (a 0 1) h01).comp (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1)))) 0) (X.gradedPiece ((CartierLift.liftHom j (a 0 0) (a 0 1) h01).comp (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1)))) 1),
      ∃ L, (X.toGradedCartierModuleData ((CartierLift.liftHom j (a 0 0) (a 0 1) h01).comp (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1)))) hc').IsCanonicalLMap L by
    have hj : (CartierLift.liftHom j (a 0 0) (a 0 1) h01).comp (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1))) = j := CartierLift.liftHom_comp_algebraMap j (a 0 0) (a 0 1) h01
    rw [hj] at H
    exact H hc
  intro hc'
  have hγ2 : X.IsHomogeneousVBasis ((CartierLift.liftHom j (a 0 0) (a 0 1) h01).comp (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1)))) γ := by
    rw [CartierLift.liftHom_comp_algebraMap]; exact hγ
  obtain ⟨_, hspl⟩ := CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1))) Xl γl hγl hcU
  obtain ⟨_, hsp⟩ := CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p ((CartierLift.liftHom j (a 0 0) (a 0 1) h01).comp (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1)))) X γ hγ2 hc'
  have hbc := CerednikDrinfeld.FormalODModule.isBaseChangeAlong_toGradedCartierModuleData_baseChange p (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1))) (CartierLift.liftHom j (a 0 0) (a 0 1) h01) Xl γl hγl hcU hcB
  obtain ⟨hgb, hgW, hgF, hgV, hgPi, hgpc⟩ :=
    CerednikDrinfeld.FormalODModule.Hom.bijective_map_and_forall_map_eq_of_isIso p ((CartierLift.liftHom j (a 0 0) (a 0 1) h01).comp (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1)))) (Xl.map (CartierLift.liftHom j (a 0 0) (a 0 1) h01)) X u hu
      (MvFormalGroup.CartierModule.map u.toLawHom) rfl
  have hcomp := CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong.comp_of_bijective p (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1))) (CartierLift.liftHom j (a 0 0) (a 0 1) h01) (Xl.toGradedCartierModuleData (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1))) hcU)
    ((Xl.map (CartierLift.liftHom j (a 0 0) (a 0 1) h01)).toGradedCartierModuleData ((CartierLift.liftHom j (a 0 0) (a 0 1) h01).comp (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1)))) hcB)
    (X.toGradedCartierModuleData ((CartierLift.liftHom j (a 0 0) (a 0 1) h01).comp (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1)))) hc')
    (MvFormalGroup.CartierModule.baseChange (Φ := Xl.F) (CartierLift.liftHom j (a 0 0) (a 0 1) h01)) hbc
    (MvFormalGroup.CartierModule.map u.toLawHom) hgb
    (fun w x => hgW w x) (fun x => hgF x) (fun x => hgV x) (fun x => hgPi x)
    (fun i x hx => hgpc (i : ℕ) x hx)
  have htf : ∀ s : (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1)), (p : (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1))) * s = 0 → s = 0 := fun s hs =>
    CartierLift.natCast_mul_eq_zero_zp2 (a 0 0) (a 0 1) s hs
  obtain ⟨Ll, hLl, -⟩ := CerednikDrinfeld.GradedCartierModuleData.existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree p (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1))) htf (Xl.toGradedCartierModuleData (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1))) hcU) hspl
  obtain ⟨L, ⟨hLf, hL⟩, -⟩ := CerednikDrinfeld.GradedCartierModuleData.existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule p (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1))) (CartierLift.liftHom j (a 0 0) (a 0 1) h01)
    (CartierLift.liftHom_surjective j (a 0 0) (a 0 1) h01)
    (Xl.toGradedCartierModuleData (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1))) hcU) hspl (X.toGradedCartierModuleData ((CartierLift.liftHom j (a 0 0) (a 0 1) h01).comp (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1)))) hc') hsp
    ((MvFormalGroup.CartierModule.map u.toLawHom).comp (MvFormalGroup.CartierModule.baseChange (Φ := Xl.F) (CartierLift.liftHom j (a 0 0) (a 0 1) h01)))
    hcomp Ll hLl
  exact ⟨L, ⟨hL, ⟨(CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1)), inferInstance, (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1))), (CartierLift.liftHom j (a 0 0) (a 0 1) h01),
    CartierLift.liftHom_surjective j (a 0 0) (a 0 1) h01, htf,
    Xl.toGradedCartierModuleData (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) (a 0 0) (a 0 1))) hcU, hspl,
    (MvFormalGroup.CartierModule.map u.toLawHom).comp (MvFormalGroup.CartierModule.baseChange (Φ := Xl.F) (CartierLift.liftHom j (a 0 0) (a 0 1) h01)),
    hcomp, Ll, hLl, hLf⟩⟩⟩

end S_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData (solution)
