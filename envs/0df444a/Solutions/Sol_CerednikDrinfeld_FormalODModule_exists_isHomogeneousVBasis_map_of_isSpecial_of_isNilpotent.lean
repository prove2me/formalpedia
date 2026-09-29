-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_map_of_isSpecial_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/b8b4f8e2-ceb5-5e20-8a3e-8834ec656347

import Mathlib
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_free_lieZero_map_and_free_lieOne_map_of_isSpecial
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_of_free_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_map_of_isSpecial_of_isNilpotent
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [Algebra ℤ_[p] B]
    (j : CerednikDrinfeld.Zp2 p →+* B) (hB : IsNilpotent (p : B)) (X : CerednikDrinfeld.FormalODModule p B)
    (hX : X.IsSpecial j) (x : PrimeSpectrum B) :
    ∃ f : B, f ∉ x.asIdeal ∧
      ∃ γ : Fin 2 → MvFormalGroup.CartierModule p (X.map (algebraMap B (Localization.Away f))).F,
        (X.map (algebraMap B (Localization.Away f))).IsHomogeneousVBasis
          ((algebraMap B (Localization.Away f)).comp j) γ := by
  obtain ⟨f, hf, h₀, h₁⟩ :=
    CerednikDrinfeld.FormalODModule.exists_free_lieZero_map_and_free_lieOne_map_of_isSpecial p j X hX x
  have hXf := CerednikDrinfeld.FormalODModule.IsSpecial.map j (algebraMap B (Localization.Away f)) X hX
  have hBf : IsNilpotent ((p : ℕ) : Localization.Away f) := by
    obtain ⟨n, hn⟩ := hB
    exact ⟨n, by rw [← map_natCast (algebraMap B (Localization.Away f)) p, ← map_pow, hn, map_zero]⟩
  obtain ⟨γ, hγ⟩ := CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_of_free_of_isNilpotent
    p _ hBf _ hXf h₀ h₁
  exact ⟨f, hf, γ, hγ⟩

end S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_map_of_isSpecial_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_map_of_isSpecial_of_isNilpotent (solution)
