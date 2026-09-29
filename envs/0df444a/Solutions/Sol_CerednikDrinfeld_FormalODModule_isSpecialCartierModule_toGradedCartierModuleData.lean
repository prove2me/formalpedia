-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/2ac98d20-6956-5ae4-8e73-9d4bbd01a407

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

import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

universe u

noncomputable section

namespace P2mModelSpecial

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime]

@[reducible] noncomputable def algebraPadicInt {B : Type} [CommRing B] (j : Zp2 p →+* B) :
    Algebra (PadicInt p) B :=
  (j.comp ((WittVector.map (algebraMap (ZMod p) (GaloisField p 2))).comp
    (WittVector.equiv p).symm.toRingHom)).toAlgebra

theorem existsUnique_digit {B : Type} [CommRing B] (j : Zp2 p →+* B) (X : FormalODModule p B)
    (γ : Fin 2 → CartierModule p X.F)
    (hγ : IsUnit (Matrix.of fun i k => tangent (γ i) k).det) (x : CartierModule p X.F) :
    ∃! cy : (Fin 2 → B) × CartierModule p X.F,
      x = (∑ i : Fin 2, WittVector.teichmuller p (cy.1 i) • γ i) + verschiebungInt cy.2 := by
  letI : Algebra (PadicInt p) B := algebraPadicInt j
  obtain ⟨ch, hch, huniq⟩ :=
    MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebungInt_iterate_homothety_add p X.F γ hγ x 1
  have e1 : ∀ (c : Fin 1 → Fin 2 → B) (y : CartierModule p X.F),
      ((∑ m : Fin 1, (⇑(verschiebungInt (p := p) (Φ := X.F)))^[(m : ℕ)]
          (∑ i : Fin 2, homothety (c m i) (γ i))) +
        (⇑(verschiebungInt (p := p) (Φ := X.F)))^[1] y) =
      (∑ i : Fin 2, WittVector.teichmuller p (c 0 i) • γ i) + verschiebungInt y := by
    intro c y
    have hs : (∑ i : Fin 2, homothety (c 0 i) (γ i)) = ∑ i : Fin 2, WittVector.teichmuller p (c 0 i) • γ i :=
      Finset.sum_congr rfl fun i _ => (teichmuller_smul _ _).symm
    rw [Fin.sum_univ_one, Fin.val_zero, Function.iterate_zero_apply, Function.iterate_one, hs]
  refine ⟨(ch.1 0, ch.2), ?_, ?_⟩
  · show x = (∑ i : Fin 2, WittVector.teichmuller p (ch.1 0 i) • γ i) + verschiebungInt ch.2
    rw [← e1]; exact hch
  · rintro ⟨c, y⟩ hcy
    have hc' := huniq (fun _ => c, y) (by show x = _; rw [e1]; exact hcy)
    have h1 : (fun _ : Fin 1 => c) = ch.1 := congrArg Prod.fst hc'
    have h2 : y = ch.2 := congrArg Prod.snd hc'
    show (c, y) = (ch.1 0, ch.2)
    rw [← h1, h2]

end P2mModelSpecial

end

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule P2mModelSpecial in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) :
    (X.toGradedCartierModuleData j hc).IsHomogeneousVBasis γ ∧
      (X.toGradedCartierModuleData j hc).IsSpecialCartierModule := by
  have hb : (X.toGradedCartierModuleData j hc).IsHomogeneousVBasis γ :=
    ⟨fun i => hγ.1 i, fun x => existsUnique_digit j X γ hγ.2 x⟩
  refine ⟨hb, ⟨γ, hb⟩, fun x => ?_⟩
  exact MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add p X.F x

end S_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData (solution)
