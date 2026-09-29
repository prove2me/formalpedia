-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_of_isBaseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/75d3ddb3-12f6-5bbe-823e-9b5792f2cb81

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Theorems.Thm_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_baseChange_of_torsionFree
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_baseChange_comp_eq_and_unique
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_isHomogeneousVBasis_map_of_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_of_isBaseChangeAlong
p2m_attr_erase "instance" "MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk MvFormalGroup.CartierModule.instModuleWittVector MvFormalGroup.instIsCommMapRingHom MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.CartierModule.toPowerSeries_sub MvFormalGroup.WittLaw.verFam_zero MvFormalGroup.WittLaw.verFam_succ MvFormalGroup.CartierModule.toPowerSeries_frobenius MvFormalGroup.CartierModule.toPowerSeries_verschiebung MvFormalGroup.WittLaw.blk_apply MvFormalGroup.WittLaw.weight_apply MvFormalGroup.CartierModule.toPowerSeries_map MvFormalGroup.CartierModule.toPowerSeries_precompFun MvFormalGroup.CartierModule.toPowerSeries_mapFun MvFormalGroup.CartierModule.mk.injEq MvFormalGroup.WittLaw.pairFam_apply MvFormalGroup.CartierModule.endAct_apply MvFormalGroup.WittLaw.frobFam_apply MvFormalGroup.CartierModule.toPowerSeries_zero MvFormalGroup.CartierModule.tangent_apply MvFormalGroup.CartierModule.toPowerSeries_precomp MvFormalGroup.CartierModule.Examples.toPowerSeries_addLinear MvFormalGroup.CartierModule.toPowerSeries_add MvFormalGroup.CartierModule.toPowerSeries_neg MvFormalGroup.CartierModule.mk.sizeOf_spec MvFormalGroup.CartierModule.inBlk_apply MvFormalGroup.WittLaw.teichFam_apply MvFormalGroup.CartierModule.toPowerSeries_homothety MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one MvFormalGroup.CartierModule.toPowerSeries_verschiebungInt MvFormalGroup.WittLaw.xTaut_coeff MvFormalGroup.WittLaw.frobPolyFam_apply MvFormalGroup.CartierModule.toPowerSeries_baseChangeEqFun"
p2m_attr_erase "simp" "MvFormalGroup.toPowerSeries_map_ringHom MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq CerednikDrinfeld.FormalODModule.mem_toGradedCartierModuleData_piece_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_homothety_apply CerednikDrinfeld.FormalODModule.mem_gradedSubmodule_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_frobenius_apply CerednikDrinfeld.FormalODModule.varpiLinear_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_varpi_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_verschiebung_apply CerednikDrinfeld.FormalODModule.gradedSubmodule_toAddSubgroup MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

namespace X2CL
open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime]

abbrev relabel {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j) (j₂ : Zp2 p →+* B) :
    GradedCartierModuleData p B j₂ where
  M := D.M
  addCommGroup := D.addCommGroup
  module := D.module
  frobenius := D.frobenius
  verschiebung := D.verschiebung
  varpi := D.varpi
  piece := D.piece
  frobenius_smul := D.frobenius_smul
  smul_verschiebung := D.smul_verschiebung
  verschiebung_smul_frobenius := D.verschiebung_smul_frobenius
  frobenius_verschiebung := D.frobenius_verschiebung
  varpi_verschiebung := D.varpi_verschiebung
  varpi_frobenius := D.varpi_frobenius
  varpi_varpi := D.varpi_varpi
  isCompl_piece := D.isCompl_piece
  verschiebung_mem := D.verschiebung_mem
  frobenius_mem := D.frobenius_mem
  varpi_mem := D.varpi_mem

theorem map_map {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') (w : WittVector p R) :
    WittVector.map f' (WittVector.map f w) = WittVector.map (f'.comp f) w := by
  ext n; simp [WittVector.map_coeff]

end X2CL

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData in

theorem solution
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B'] (j : CerednikDrinfeld.Zp2 p →+* B)
    (φ : B →+* B')
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' (φ.comp j)) (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) :
    ∃ L' : D'.M →+ D'.NMod, D'.IsCanonicalLMap L' := by
  classical

  obtain ⟨S₀, _, jS₀, φ₀, hφ₀, htf₀, Dl₀, hDl₀, f₀, hf₀, Ll₀, hLl₀, -⟩ := hL.exists_lift

  obtain ⟨T, _, i, qT, htfT, hqT, hqi⟩ :=
    CerednikDrinfeld.exists_torsionFree_surjective_comp_eq p (φ.comp φ₀) htf₀

  obtain ⟨DT, hDT, gT, hgT⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.exists_isSpecialCartierModule_and_baseChange_of_torsionFree p
      (i.comp jS₀) i htf₀ Dl₀ hDl₀

  have hf' : IsBaseChangeAlong' φ D D' f := hf
  have hk : IsBaseChangeAlong' (qT.comp i) Dl₀ D' (f.comp f₀) := by
    rw [hqi]
    refine ⟨fun w x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun l x hx => ?_, ?_⟩
    · show f (f₀ (w • x)) = _
      rw [hf₀.1, hf.1, X2CL.map_map]
      rfl
    · show f (f₀ (Dl₀.frobenius x)) = D'.frobenius (f (f₀ x))
      rw [hf₀.2.1, hf.2.1]
    · show f (f₀ (Dl₀.verschiebung x)) = D'.verschiebung (f (f₀ x))
      rw [hf₀.2.2.1, hf.2.2.1]
    · show f (f₀ (Dl₀.varpi x)) = D'.varpi (f (f₀ x))
      rw [hf₀.2.2.2.1, hf.2.2.2.1]
    · exact hf.2.2.2.2.1 l _ (hf₀.2.2.2.2.1 l x hx)
    · obtain ⟨γ₀, hγ₀, hγ₀D⟩ := hf₀.2.2.2.2.2
      exact ⟨γ₀, hγ₀, CerednikDrinfeld.GradedCartierModuleData.isHomogeneousVBasis_map_of_baseChange p φ D hD D' hD' f hf' _ hγ₀D⟩

  obtain ⟨h, hh, hhg, -⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.exists_baseChange_comp_eq_and_unique p i qT Dl₀ hDl₀ DT hDT D' hD' gT hgT
      (f.comp f₀) hk

  obtain ⟨LT, hLT, -⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree p
      (i.comp jS₀) htfT DT hDT
  have hD'' : (X2CL.relabel D' (qT.comp (i.comp jS₀))).IsSpecialCartierModule := hD'
  have hh'' : IsBaseChangeAlong qT DT (X2CL.relabel D' (qT.comp (i.comp jS₀))) h := hh
  obtain ⟨L', ⟨hL'h, hL'⟩, -⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule
      p (i.comp jS₀) qT hqT DT hDT (X2CL.relabel D' (qT.comp (i.comp jS₀))) hD'' h hh'' LT hLT
  refine ⟨L', ⟨⟨hL'.1, hL'.2, hL'.3⟩, ⟨T, inferInstance, i.comp jS₀, qT, hqT, htfT, DT, hDT, h, hh, LT, hLT, fun x => hL'h x⟩⟩⟩

end S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_of_isBaseChangeAlong
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_of_isBaseChangeAlong (solution)
