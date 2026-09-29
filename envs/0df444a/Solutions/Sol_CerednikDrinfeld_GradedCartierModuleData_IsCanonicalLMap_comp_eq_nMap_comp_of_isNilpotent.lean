-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/bfcde621-efc7-5c40-a150-8582cac41255

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_apply_comp_eq_nMap_apply_of_torsionFree
import Theorems.Thm_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_baseChange_of_torsionFree
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_baseChange_comp_eq_and_unique
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_apply_comp_eq_nMap_apply_of_torsionFree
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_comp_eq_nMap_comp_of_forall_apply_basis_eq
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_isHomogeneousVBasis_map_of_baseChange
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_isNilpotent
p2m_attr_erase "instance" "MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk MvFormalGroup.CartierModule.instModuleWittVector MvFormalGroup.instIsCommMapRingHom MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.CartierModule.toPowerSeries_sub MvFormalGroup.WittLaw.verFam_zero MvFormalGroup.WittLaw.verFam_succ MvFormalGroup.CartierModule.toPowerSeries_frobenius MvFormalGroup.CartierModule.toPowerSeries_verschiebung MvFormalGroup.WittLaw.blk_apply MvFormalGroup.WittLaw.weight_apply MvFormalGroup.CartierModule.toPowerSeries_map MvFormalGroup.CartierModule.toPowerSeries_precompFun MvFormalGroup.CartierModule.toPowerSeries_mapFun MvFormalGroup.CartierModule.mk.injEq MvFormalGroup.WittLaw.pairFam_apply MvFormalGroup.CartierModule.endAct_apply MvFormalGroup.WittLaw.frobFam_apply MvFormalGroup.CartierModule.toPowerSeries_zero MvFormalGroup.CartierModule.tangent_apply MvFormalGroup.CartierModule.toPowerSeries_precomp MvFormalGroup.CartierModule.Examples.toPowerSeries_addLinear MvFormalGroup.CartierModule.toPowerSeries_add MvFormalGroup.CartierModule.toPowerSeries_neg MvFormalGroup.CartierModule.mk.sizeOf_spec MvFormalGroup.CartierModule.inBlk_apply MvFormalGroup.WittLaw.teichFam_apply MvFormalGroup.CartierModule.toPowerSeries_homothety MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one MvFormalGroup.CartierModule.toPowerSeries_verschiebungInt MvFormalGroup.WittLaw.xTaut_coeff MvFormalGroup.WittLaw.frobPolyFam_apply MvFormalGroup.CartierModule.toPowerSeries_baseChangeEqFun"
p2m_attr_erase "simp" "MvFormalGroup.toPowerSeries_map_ringHom MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq CerednikDrinfeld.FormalODModule.mem_toGradedCartierModuleData_piece_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_homothety_apply CerednikDrinfeld.FormalODModule.mem_gradedSubmodule_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_frobenius_apply CerednikDrinfeld.FormalODModule.varpiLinear_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_varpi_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_verschiebung_apply CerednikDrinfeld.FormalODModule.gradedSubmodule_toAddSubgroup MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

namespace NatLReduce

variable {p : ℕ} [Fact p.Prime]

theorem nMap_nMap_apply {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    {j₁ : Zp2 p →+* R₁} {j₂ : Zp2 p →+* R₂} {j₃ : Zp2 p →+* R₃}
    (D₁ : GradedCartierModuleData p R₁ j₁) (D₂ : GradedCartierModuleData p R₂ j₂)
    (D₃ : GradedCartierModuleData p R₃ j₃)
    (a : D₁.M →+ D₂.M) (haV : ∀ x, a (D₁.verschiebung x) = D₂.verschiebung (a x))
    (haP : ∀ x, a (D₁.varpi x) = D₂.varpi (a x))
    (b : D₂.M →+ D₃.M) (hbV : ∀ x, b (D₂.verschiebung x) = D₃.verschiebung (b x))
    (hbP : ∀ x, b (D₂.varpi x) = D₃.varpi (b x))
    (c : D₁.M →+ D₃.M) (hcV : ∀ x, c (D₁.verschiebung x) = D₃.verschiebung (c x))
    (hcP : ∀ x, c (D₁.varpi x) = D₃.varpi (c x))
    (hbc : ∀ x, b (a x) = c x) (n : D₁.NMod) :
    D₂.nMap D₃ b hbV hbP (D₁.nMap D₂ a haV haP n) = D₁.nMap D₃ c hcV hcP n := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D₁.nMk_surjective n
  rw [nMap_nMk, nMap_nMk, nMap_nMk, hbc, hbc]

theorem nMap_id_apply {R : Type} [CommRing R] {j : Zp2 p →+* R} (D : GradedCartierModuleData p R j)
    (hV : ∀ x, (AddMonoidHom.id D.M) (D.verschiebung x) = D.verschiebung ((AddMonoidHom.id D.M) x))
    (hP : ∀ x, (AddMonoidHom.id D.M) (D.varpi x) = D.varpi ((AddMonoidHom.id D.M) x)) (n : D.NMod) :
    D.nMap D (AddMonoidHom.id D.M) hV hP n = n := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective n
  rw [nMap_nMk]
  rfl

theorem isBaseChangeAlong'_id {R : Type} [CommRing R] {j : Zp2 p →+* R} (D : GradedCartierModuleData p R j)
    (hD : D.IsSpecialCartierModule) :
    IsBaseChangeAlong' (RingHom.id R) D D (AddMonoidHom.id D.M) := by
  have hmap : ∀ w : WittVector p R, WittVector.map (RingHom.id R) w = w := fun w => by
    ext n; simp
  refine ⟨fun w x => ?_, fun x => rfl, fun x => rfl, fun x => rfl, fun i x hx => hx, ?_⟩
  · rw [hmap]; rfl
  · obtain ⟨γ, hγ⟩ := hD.1
    exact ⟨γ, hγ, hγ⟩

end NatLReduce

open NatLReduce

theorem solution
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B']
    (j : CerednikDrinfeld.Zp2 p →+* B) (φ : B →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' (φ.comp j)) (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (L' : D'.M →+ D'.NMod) (hL' : D'.IsCanonicalLMap L') :
    ∀ x : D.M, L' (f x) = D.nMap D' f hf.2.2.1 hf.2.2.2.1 (L x) := by
  classical
  have wmap : ∀ {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (a : R₁ →+* R₂) (b : R₂ →+* R₃)
      (w : WittVector p R₁), WittVector.map b (WittVector.map a w) = WittVector.map (b.comp a) w := by
    intro R₁ R₂ R₃ _ _ _ a b w
    ext n
    simp [WittVector.map_coeff]

  have hf' : IsBaseChangeAlong' φ D D' f :=
    ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2⟩

  obtain ⟨S, _iS, jS, ψ, hψ, hS, Dl, hDl, g, hg, Ll, hLl, hP⟩ := hL.exists_lift
  obtain ⟨γo, hγo, hgγo⟩ := hg.2.2.2.2.2

  obtain ⟨T, _iT, ι, q, hT, hq, hqι⟩ := CerednikDrinfeld.exists_torsionFree_surjective_comp_eq p (φ.comp ψ) hS

  obtain ⟨E, hE, gE, hgE⟩ :=
    GradedCartierModuleData.exists_isSpecialCartierModule_and_baseChange_of_torsionFree
      p (ι.comp jS) ι hS Dl hDl
  have hcV : ∀ x, (f.comp g) (Dl.verschiebung x) = D'.verschiebung ((f.comp g) x) := fun x => by
    simp only [AddMonoidHom.comp_apply, hg.2.2.1, hf.2.2.1]
  have hcP : ∀ x, (f.comp g) (Dl.varpi x) = D'.varpi ((f.comp g) x) := fun x => by
    simp only [AddMonoidHom.comp_apply, hg.2.2.2.1, hf.2.2.2.1]
  have hk : IsBaseChangeAlong' (q.comp ι) Dl D' (f.comp g) := by
    rw [hqι]
    refine ⟨fun w x => ?_, fun x => ?_, hcV, hcP, fun i x hx => ?_, ?_⟩
    · simp only [AddMonoidHom.comp_apply, hg.1, hf.1, wmap]
    · simp only [AddMonoidHom.comp_apply, hg.2.1, hf.2.1]
    · exact hf.2.2.2.2.1 i _ (hg.2.2.2.2.1 i x hx)
    · exact ⟨γo, hγo, GradedCartierModuleData.isHomogeneousVBasis_map_of_baseChange
        p φ D hD D' hD' f hf' (fun i => g (γo i)) hgγo⟩
  obtain ⟨F, hF, hFg, -⟩ :=
    GradedCartierModuleData.exists_baseChange_comp_eq_and_unique
      p ι q Dl hDl E hE D' hD' gE hgE (f.comp g) hk
  obtain ⟨LE, hLE⟩ :=
    (GradedCartierModuleData.existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree
      p (ι.comp jS) hT E hE).exists

  have hC := GradedCartierModuleData.IsCanonicalLMap.apply_comp_eq_nMap_apply_of_torsionFree
    p q hq hT D' hD' E hE F hF LE hLE L' hL'
  have hLg := GradedCartierModuleData.IsCartierLMap.apply_comp_eq_nMap_apply_of_torsionFree
    p ι hT Dl hDl E hE gE hgE Ll hLl LE hLE

  have key := GradedCartierModuleData.IsCartierLMap.comp_eq_nMap_comp_of_forall_apply_basis_eq
    p φ D D' f hf' L hL.isCartierLMap L' hL'.isCartierLMap (fun i => g (γo i)) hgγo (fun i => by
      have h1 : f (g (γo i)) = F (gE (γo i)) := by rw [hFg]; rfl
      rw [h1, hC, hLg, hP,
        nMap_nMap_apply Dl E D' gE hgE.2.2.1 hgE.2.2.2.1 F hF.2.2.1 hF.2.2.2.1 (f.comp g) hcV hcP
          (fun x => hFg x),
        nMap_nMap_apply Dl D D' g hg.2.2.1 hg.2.2.2.1 f hf'.2.2.1 hf'.2.2.2.1 (f.comp g) hcV hcP
          (fun x => rfl)])
  intro x
  exact key x

end S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_isNilpotent (solution)
