-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_hom_isIso_forall_map_eq_of_hasStructureConstants
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/84a400f1-9735-526e-9cea-cf65d81fe0ed

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
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hom_isIso_forall_map_eq_of_bijective
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_isIso_forall_map_eq_of_hasStructureConstants
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hsep : IsHausdorff (Ideal.span {(p : B)}) B)
    (X X' : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F)
    (γ' : Fin 2 → MvFormalGroup.CartierModule p X'.F)
    (hγ : X.IsHomogeneousVBasis j γ) (hγ' : X'.IsHomogeneousVBasis j γ')
    (a : ℕ → Fin 2 → B)
    (ha : X.HasStructureConstants γ a) (ha' : X'.HasStructureConstants γ' a) :
    ∃ u : X.Hom X', u.IsIso ∧
      ∀ i : Fin 2, MvFormalGroup.CartierModule.map u.toLawHom (γ i) = γ' i := by
  obtain ⟨θ, hbij, hγγ, hF, hV, hH, hA, hPi⟩ :=
    CerednikDrinfeld.FormalODModule.exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants
      p j hsep X X' γ γ' hγ hγ' a ha ha'
  obtain ⟨u, hu, hmap⟩ :=
    CerednikDrinfeld.FormalODModule.exists_hom_isIso_forall_map_eq_of_bijective p j X X' θ hbij hF hV hH hA hPi
  exact ⟨u, hu, fun i => by rw [hmap, hγγ]⟩

end S_CerednikDrinfeld_FormalODModule_exists_hom_isIso_forall_map_eq_of_hasStructureConstants
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_isIso_forall_map_eq_of_hasStructureConstants (solution)
