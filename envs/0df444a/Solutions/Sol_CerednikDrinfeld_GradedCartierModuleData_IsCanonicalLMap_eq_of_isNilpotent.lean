-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.eq_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6423f103-2dcd-5801-b46a-703a459e3a53

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_comp_eq_nMap_comp_of_forall_apply_basis_eq
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_baseChange_comp_eq_and_unique
import Theorems.Thm_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_and_comp_eq_of_surjective
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_dominating_of_apply_basis_eq
import Theorems.Thm_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_forall_isUnit
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_isHomogeneousVBasis_apply_eq_of_forall_isUnit
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_baseChange_of_torsionFree
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_apply_comp_eq_nMap_apply_of_torsionFree
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_eq_of_isNilpotent
p2m_attr_erase "instance" "MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk MvFormalGroup.CartierModule.instModuleWittVector MvFormalGroup.instIsCommMapRingHom MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.CartierModule.toPowerSeries_sub MvFormalGroup.WittLaw.verFam_zero MvFormalGroup.WittLaw.verFam_succ MvFormalGroup.CartierModule.toPowerSeries_frobenius MvFormalGroup.CartierModule.toPowerSeries_verschiebung MvFormalGroup.WittLaw.blk_apply MvFormalGroup.WittLaw.weight_apply MvFormalGroup.CartierModule.toPowerSeries_map MvFormalGroup.CartierModule.toPowerSeries_precompFun MvFormalGroup.CartierModule.toPowerSeries_mapFun MvFormalGroup.CartierModule.mk.injEq MvFormalGroup.WittLaw.pairFam_apply MvFormalGroup.CartierModule.endAct_apply MvFormalGroup.WittLaw.frobFam_apply MvFormalGroup.CartierModule.toPowerSeries_zero MvFormalGroup.CartierModule.tangent_apply MvFormalGroup.CartierModule.toPowerSeries_precomp MvFormalGroup.CartierModule.Examples.toPowerSeries_addLinear MvFormalGroup.CartierModule.toPowerSeries_add MvFormalGroup.CartierModule.toPowerSeries_neg MvFormalGroup.CartierModule.mk.sizeOf_spec MvFormalGroup.CartierModule.inBlk_apply MvFormalGroup.WittLaw.teichFam_apply MvFormalGroup.CartierModule.toPowerSeries_homothety MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one MvFormalGroup.CartierModule.toPowerSeries_verschiebungInt MvFormalGroup.WittLaw.xTaut_coeff MvFormalGroup.WittLaw.frobPolyFam_apply MvFormalGroup.CartierModule.toPowerSeries_baseChangeEqFun"
p2m_attr_erase "simp" "MvFormalGroup.toPowerSeries_map_ringHom MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq CerednikDrinfeld.FormalODModule.mem_toGradedCartierModuleData_piece_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_homothety_apply CerednikDrinfeld.FormalODModule.mem_gradedSubmodule_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_frobenius_apply CerednikDrinfeld.FormalODModule.varpiLinear_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_varpi_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_verschiebung_apply CerednikDrinfeld.FormalODModule.gradedSubmodule_toAddSubgroup MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

namespace C6dReduce

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

end C6dReduce

open C6dReduce

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : IsNilpotent (p : B))
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (L L' : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) (hL' : D.IsCanonicalLMap L') :
    L = L' := by
  classical

  obtain ⟨S₁, _i₁, jS₁, φ₁, hφ₁, hS₁, Dl₁, hDl₁, f₁, hf₁, Ll₁, hLl₁, hP₁⟩ := hL.exists_lift
  obtain ⟨S₂, _i₂, jS₂, φ₂, hφ₂, hS₂, Dl₂, hDl₂, f₂, hf₂, Ll₂, hLl₂, hP₂⟩ := hL'.exists_lift

  obtain ⟨T₁, _iT₁, ι₁, jT₁, q₁, hT₁, hq₁s, hq₁ι, hq₁j⟩ :=
    CerednikDrinfeld.exists_torsionFree_surjective_comp_eq_and_comp_eq_of_surjective p φ₁ hφ₁ hS₁ j
  obtain ⟨U₁, _iU₁, ι₁', u₁, hU₁, hu₁s, hu₁ι, hu₁det⟩ :=
    CerednikDrinfeld.exists_torsionFree_surjective_comp_eq_forall_isUnit p q₁ hq₁s hT₁
  have hju₁ : u₁.comp (ι₁'.comp jT₁) = j := by
    rw [← RingHom.comp_assoc, hu₁ι, hq₁j]
  have hφ₁eq : u₁.comp (ι₁'.comp ι₁) = φ₁ := by
    rw [← RingHom.comp_assoc, hu₁ι, hq₁ι]

  obtain ⟨E₁, hE₁, g₁, hg₁⟩ :=
    GradedCartierModuleData.exists_isSpecialCartierModule_and_baseChange_of_torsionFree
      p (ι₁'.comp jT₁) (ι₁'.comp ι₁) hS₁ Dl₁ hDl₁
  have hk₁ : IsBaseChangeAlong' (u₁.comp (ι₁'.comp ι₁)) Dl₁ D f₁ := by rw [hφ₁eq]; exact hf₁
  obtain ⟨F₁, hF₁, hF₁g, -⟩ :=
    GradedCartierModuleData.exists_baseChange_comp_eq_and_unique
      p (ι₁'.comp ι₁) u₁ Dl₁ hDl₁ E₁ hE₁ D hD g₁ hg₁ f₁ hk₁
  obtain ⟨LE₁, hLE₁⟩ :=
    (GradedCartierModuleData.existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree
      p (ι₁'.comp jT₁) hU₁ E₁ hE₁).exists

  have hP₁' : ∀ y : E₁.M, L (F₁ y) = E₁.nMap D F₁ hF₁.2.2.1 hF₁.2.2.2.1 (LE₁ y) := by
    obtain ⟨γo, hγo, hgγo⟩ := hg₁.2.2.2.2.2
    refine GradedCartierModuleData.IsCartierLMap.comp_eq_nMap_comp_of_forall_apply_basis_eq
      p u₁ E₁ D F₁ hF₁ LE₁ hLE₁ L hL.isCartierLMap (fun i => g₁ (γo i)) hgγo (fun i => ?_)
    rw [hF₁g, hP₁,
      GradedCartierModuleData.IsCartierLMap.apply_comp_eq_nMap_apply_of_torsionFree
        p (ι₁'.comp ι₁) hU₁ Dl₁ hDl₁ E₁ hE₁ g₁ hg₁ Ll₁ hLl₁ LE₁ hLE₁,
      nMap_nMap_apply Dl₁ E₁ D g₁ hg₁.2.2.1 hg₁.2.2.2.1 F₁ hF₁.2.2.1 hF₁.2.2.2.1
        f₁ hf₁.2.2.1 hf₁.2.2.2.1 hF₁g]

  obtain ⟨T₂, _iT₂, ι₂, jT₂, q₂, hT₂, hq₂s, hq₂ι, hq₂j⟩ :=
    CerednikDrinfeld.exists_torsionFree_surjective_comp_eq_and_comp_eq_of_surjective p φ₂ hφ₂ hS₂ j
  obtain ⟨E₂, hE₂, g₂, hg₂⟩ :=
    GradedCartierModuleData.exists_isSpecialCartierModule_and_baseChange_of_torsionFree
      p jT₂ ι₂ hS₂ Dl₂ hDl₂
  have hk₂ : IsBaseChangeAlong' (q₂.comp ι₂) Dl₂ D f₂ := by rw [hq₂ι]; exact hf₂
  obtain ⟨F₂, hF₂, hF₂g, -⟩ :=
    GradedCartierModuleData.exists_baseChange_comp_eq_and_unique
      p ι₂ q₂ Dl₂ hDl₂ E₂ hE₂ D hD g₂ hg₂ f₂ hk₂
  obtain ⟨LE₂, hLE₂⟩ :=
    (GradedCartierModuleData.existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree
      p jT₂ hT₂ E₂ hE₂).exists
  have hP₂' : ∀ y : E₂.M, L' (F₂ y) = E₂.nMap D F₂ hF₂.2.2.1 hF₂.2.2.2.1 (LE₂ y) := by
    obtain ⟨γo, hγo, hgγo⟩ := hg₂.2.2.2.2.2
    refine GradedCartierModuleData.IsCartierLMap.comp_eq_nMap_comp_of_forall_apply_basis_eq
      p q₂ E₂ D F₂ hF₂ LE₂ hLE₂ L' hL'.isCartierLMap (fun i => g₂ (γo i)) hgγo (fun i => ?_)
    rw [hF₂g, hP₂,
      GradedCartierModuleData.IsCartierLMap.apply_comp_eq_nMap_apply_of_torsionFree
        p ι₂ hT₂ Dl₂ hDl₂ E₂ hE₂ g₂ hg₂ Ll₂ hLl₂ LE₂ hLE₂,
      nMap_nMap_apply Dl₂ E₂ D g₂ hg₂.2.2.1 hg₂.2.2.2.1 F₂ hF₂.2.2.1 hF₂.2.2.2.1
        f₂ hf₂.2.2.1 hf₂.2.2.2.1 hF₂g]

  obtain ⟨γ₂, hγ₂, hβ⟩ := hF₂.2.2.2.2.2
  obtain ⟨γ₁, hγ₁, hγ₁₂⟩ :=
    GradedCartierModuleData.exists_isHomogeneousVBasis_apply_eq_of_forall_isUnit
      p u₁ hu₁s hu₁det E₁ hE₁ D hD F₁ hF₁ (fun i => F₂ (γ₂ i)) hβ

  obtain ⟨S₃, _i₃, j₃, r₁, r₂, hr₁, hr₂, hqr, hS₃, D₃, hD₃, γ₃, hγ₃, G₁, G₂, hG₁, hG₂, hG₁γ, hG₂γ, hFG⟩ :=
    GradedCartierModuleData.exists_dominating_of_apply_basis_eq
      p j (ι₁'.comp jT₁) jT₂ u₁ q₂ hju₁ hq₂j hU₁ hT₂ D hD E₁ hE₁ E₂ hE₂ F₁ hF₁ F₂ hF₂ γ₁ hγ₁ γ₂ hγ₂ hγ₁₂
  obtain ⟨L₃, hL₃⟩ :=
    (GradedCartierModuleData.existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree
      p j₃ hS₃ D₃ hD₃).exists
  have hLG₁ := GradedCartierModuleData.IsCartierLMap.apply_comp_eq_nMap_apply_of_torsionFree
    p r₁ hU₁ D₃ hD₃ E₁ hE₁ G₁ hG₁ L₃ hL₃ LE₁ hLE₁
  have hLG₂ := GradedCartierModuleData.IsCartierLMap.apply_comp_eq_nMap_apply_of_torsionFree
    p r₂ hT₂ D₃ hD₃ E₂ hE₂ G₂ hG₂ L₃ hL₃ LE₂ hLE₂

  have hcV : ∀ x, (F₁.comp G₁) (D₃.verschiebung x) = D.verschiebung ((F₁.comp G₁) x) := fun x => by
    simp only [AddMonoidHom.comp_apply, hG₁.2.2.1, hF₁.2.2.1]
  have hcP : ∀ x, (F₁.comp G₁) (D₃.varpi x) = D.varpi ((F₁.comp G₁) x) := fun x => by
    simp only [AddMonoidHom.comp_apply, hG₁.2.2.2.1, hF₁.2.2.2.1]

  have hKey : ∀ y : E₁.M, L' (F₁ y) = E₁.nMap D F₁ hF₁.2.2.1 hF₁.2.2.2.1 (LE₁ y) := by
    refine GradedCartierModuleData.IsCartierLMap.comp_eq_nMap_comp_of_forall_apply_basis_eq
      p u₁ E₁ D F₁ hF₁ LE₁ hLE₁ L' hL'.isCartierLMap γ₁ hγ₁ (fun i => ?_)
    calc L' (F₁ (γ₁ i)) = L' (F₁ (G₁ (γ₃ i))) := by rw [hG₁γ]
      _ = L' (F₂ (G₂ (γ₃ i))) := by rw [hFG]
      _ = E₂.nMap D F₂ hF₂.2.2.1 hF₂.2.2.2.1 (LE₂ (G₂ (γ₃ i))) := hP₂' _
      _ = E₂.nMap D F₂ hF₂.2.2.1 hF₂.2.2.2.1
            (D₃.nMap E₂ G₂ hG₂.2.2.1 hG₂.2.2.2.1 (L₃ (γ₃ i))) := by rw [hLG₂]
      _ = D₃.nMap D (F₁.comp G₁) hcV hcP (L₃ (γ₃ i)) :=
            nMap_nMap_apply D₃ E₂ D G₂ hG₂.2.2.1 hG₂.2.2.2.1 F₂ hF₂.2.2.1 hF₂.2.2.2.1
              (F₁.comp G₁) hcV hcP (fun x => (hFG x).symm) _
      _ = E₁.nMap D F₁ hF₁.2.2.1 hF₁.2.2.2.1
            (D₃.nMap E₁ G₁ hG₁.2.2.1 hG₁.2.2.2.1 (L₃ (γ₃ i))) :=
            (nMap_nMap_apply D₃ E₁ D G₁ hG₁.2.2.1 hG₁.2.2.2.1 F₁ hF₁.2.2.1 hF₁.2.2.2.1
              (F₁.comp G₁) hcV hcP (fun x => rfl) _).symm
      _ = E₁.nMap D F₁ hF₁.2.2.1 hF₁.2.2.2.1 (LE₁ (G₁ (γ₃ i))) := by rw [hLG₁]
      _ = E₁.nMap D F₁ hF₁.2.2.1 hF₁.2.2.2.1 (LE₁ (γ₁ i)) := by rw [hG₁γ]

  have hid := isBaseChangeAlong'_id D hD
  have hβ₁ : D.IsHomogeneousVBasis (fun i => F₁ (γ₁ i)) := by
    have : (fun i => F₁ (γ₁ i)) = (fun i => F₂ (γ₂ i)) := funext hγ₁₂
    rw [this]; exact hβ
  have hfin := GradedCartierModuleData.IsCartierLMap.comp_eq_nMap_comp_of_forall_apply_basis_eq
    p (RingHom.id B) D D (AddMonoidHom.id D.M) hid L' hL'.isCartierLMap L hL.isCartierLMap
    (fun i => F₁ (γ₁ i)) hβ₁ (fun i => by
      rw [AddMonoidHom.id_apply, nMap_id_apply, hP₁' (γ₁ i), hKey (γ₁ i)])
  ext x
  have hx := hfin x
  rw [AddMonoidHom.id_apply, nMap_id_apply] at hx
  exact hx

end S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_eq_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_eq_of_isNilpotent (solution)
