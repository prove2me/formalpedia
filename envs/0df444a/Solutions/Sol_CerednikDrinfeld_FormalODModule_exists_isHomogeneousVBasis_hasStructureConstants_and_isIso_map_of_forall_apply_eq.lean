-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_hasStructureConstants_and_isIso_map_of_forall_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/b5a3a51a-aa03-5711-9421-cd6bbc4706fc

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
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hom_isIso_forall_map_eq_of_hasStructureConstants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_and_isIso_map_of_forall_apply_eq
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.FormalODModule MvFormalGroup.CartierModule

theorem solution
    (p : ℕ) [Fact p.Prime] {B B' : Type u} [CommRing B] [CommRing B']
    (j' : CerednikDrinfeld.Zp2 p →+* B') (φ : B' →+* B)
    (hsep : IsHausdorff (Ideal.span {(p : B)}) B)
    (X : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis (φ.comp j') γ)
    (a : ℕ → Fin 2 → B) (ha : X.HasStructureConstants γ a)
    (a' : ℕ → Fin 2 → B') (ha' : ∀ m i, φ (a' m i) = a m i) (h01 : a' 0 0 * a' 0 1 = (p : B')) :
    ∃ (X' : CerednikDrinfeld.FormalODModule p B') (γ' : Fin 2 → MvFormalGroup.CartierModule p X'.F),
      X'.IsHomogeneousVBasis j' γ' ∧ X'.HasStructureConstants γ' a' ∧
        ∃ u : (X'.map φ).Hom X, u.IsIso ∧ ∀ i : Fin 2,
          MvFormalGroup.CartierModule.map u.toLawHom
            (MvFormalGroup.CartierModule.baseChange φ (γ' i)) = γ i := by
  obtain ⟨X', γ', hγ', ha''⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq p j' a' h01
  refine ⟨X', γ', hγ', ha'', ?_⟩
  have hγb := hγ'.map φ
  have hab := ha''.map φ
  have hconst : (fun m i => φ (a' m i)) = a := funext fun m => funext fun i => ha' m i
  rw [hconst] at hab
  obtain ⟨u, hu, hγu⟩ :=
    CerednikDrinfeld.FormalODModule.exists_hom_isIso_forall_map_eq_of_hasStructureConstants p (φ.comp j') hsep
      (X'.map φ) X _ γ hγb hγ a hab ha
  exact ⟨u, hu, hγu⟩

end S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_and_isIso_map_of_forall_apply_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_and_isIso_map_of_forall_apply_eq (solution)
