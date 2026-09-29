-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.exists_formalODModule_bijective_of_isSpecialCartierModule_of_torsionFree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/76ebad60-a189-5243-9f3e-110713be2f72

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
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_formalODModule_bijective_of_isSpecialCartierModule_of_torsionFree
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

namespace B29AIM

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

theorem hasStructureConstants_toGradedCartierModuleData {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]
    (j : Zp2 p →+* B) (X : FormalODModule p B) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (γ : Fin 2 → CartierModule p X.F) (a : ℕ → Fin 2 → B) (ha : X.HasStructureConstants γ a) :
    (X.toGradedCartierModuleData j hc).HasStructureConstants γ a := by
  intro i N
  obtain ⟨h, hh⟩ := ha i N
  refine ⟨h, ?_⟩
  have e : (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := X.F)))^[(m : ℕ)]
      (homothety (a m i) (γ (FormalODModule.piIndex m i)))) =
      ∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := X.F)))^[(m : ℕ)]
        (WittVector.teichmuller p (a m i) • γ (FormalODModule.piIndex m i)) :=
    Finset.sum_congr rfl fun m _ => by rw [teichmuller_smul]
  rw [e] at hh
  exact hh

end B29AIM

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : ∀ b : B, (p : B) * b = 0 → b = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule) :
    ∃ (X : CerednikDrinfeld.FormalODModule p B) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
      (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (_ : X.IsHomogeneousVBasis j γ)
      (g : (X.toGradedCartierModuleData j hc).M →+ D.M),
      Function.Bijective g ∧
      (∀ (w : WittVector p B) (x : (X.toGradedCartierModuleData j hc).M), g (w • x) = w • g x) ∧
      (∀ x, g ((X.toGradedCartierModuleData j hc).frobenius x) = D.frobenius (g x)) ∧
      (∀ x, g ((X.toGradedCartierModuleData j hc).verschiebung x) = D.verschiebung (g x)) ∧
      (∀ x, g ((X.toGradedCartierModuleData j hc).varpi x) = D.varpi (g x)) ∧
      (∀ (i : Fin 2) (x : (X.toGradedCartierModuleData j hc).M), x ∈ (X.toGradedCartierModuleData j hc).piece i → g x ∈ D.piece i) := by
  obtain ⟨γD, hγD⟩ := hD.1
  obtain ⟨a, ha, hmul⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis p j D hD γD hγD
  obtain ⟨X, γ, hγ, haX⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq p j a hmul
  have hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis p j X γ hγ
  obtain ⟨hγ', hsp⟩ :=
    CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p j X γ hγ hc
  have haX' := B29AIM.hasStructureConstants_toGradedCartierModuleData j X hc γ a haX
  obtain ⟨g, -, hbij, hsmul, hF, hV, hPi, hpiece⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree
      p j hB (X.toGradedCartierModuleData j hc) D hsp hD γ hγ' γD hγD a haX' ha
  exact ⟨X, hc, γ, hγ, g, hbij, hsmul, hF, hV, hPi, hpiece⟩

end S_CerednikDrinfeld_GradedCartierModuleData_exists_formalODModule_bijective_of_isSpecialCartierModule_of_torsionFree
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_formalODModule_bijective_of_isSpecialCartierModule_of_torsionFree (solution)
