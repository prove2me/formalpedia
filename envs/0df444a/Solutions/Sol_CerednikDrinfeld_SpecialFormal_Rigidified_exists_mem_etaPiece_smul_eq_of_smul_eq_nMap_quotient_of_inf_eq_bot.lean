-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_mem_etaPiece_smul_eq_of_smul_eq_nMap_quotient_of_inf_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/e7413544-1058-5567-9f72-31e9e263bd76

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_nsmul_eq_zero_of_mem_eta
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_mem_eta_nMap_eq_of_nMap_eq_nMap
import Theorems.Thm_MvFormalGroup_CartierModule_exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor
import Theorems.Thm_MvFormalGroup_CartierModule_baseChange_surjective_of_surjective
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_mem_etaPiece_add_eq
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_isCompl_nPiece_zero_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_mem_etaPiece_smul_eq_of_smul_eq_nMap_quotient_of_inf_eq_bot
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace MilnorPatchKit

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [Fact p.Prime]

theorem isBaseChangeAlong'_of_eq {B S : Type} [CommRing B] [CommRing S] (j : Zp2 p →+* B)
    (g : B →+* S) (X : FormalODModule p B)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (X' : FormalODModule p S) (hX : X.map g = X') (j' : Zp2 p →+* S) (hj : g.comp j = j')
    (hc' : IsCompl (X'.gradedPiece j' 0) (X'.gradedPiece j' 1))
    (hF : X.F.map g = X'.F) :
    IsBaseChangeAlong' g (X.toGradedCartierModuleData j hc) (X'.toGradedCartierModuleData j' hc')
      (CartierModule.baseChangeEq g hF) := by
  subst hX; subst hj
  exact CerednikDrinfeld.FormalODModule.isBaseChangeAlong_toGradedCartierModuleData_baseChange p j g X γ hγ hc hc'

theorem natL_of_eq {B B' : Type} [CommRing B] [CommRing B'] (j : Zp2 p →+* B) (φ : B →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
    (D : GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (j' : Zp2 p →+* B') (hj : φ.comp j = j')
    (D' : GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : IsBaseChangeAlong' φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (L' : D'.M →+ D'.NMod) (hL' : D'.IsCanonicalLMap L') :
    ∀ x : D.M, L' (f x) = D.nMap D' f hf.2.2.1 hf.2.2.2.1 (L x) := by
  subst hj
  exact CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_isNilpotent p j φ hB hB' D hD D' hD' f hf L hL L' hL'

omit [Fact p.Prime] in
theorem isHausdorff_of_isNilpotent {S : Type} [CommRing S] (hS : IsNilpotent ((p : ℕ) : S)) :
    IsHausdorff (Ideal.span {((p : ℕ) : S)}) S := by
  obtain ⟨N, hN⟩ := hS
  refine ⟨fun x hx => ?_⟩
  have := hx N
  rwa [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

theorem isHomogeneousVBasis_push {B S : Type} [CommRing B] [CommRing S] {j : Zp2 p →+* B} {j' : Zp2 p →+* S}
    (g : B →+* S) (X : FormalODModule p B) (X' : FormalODModule p S)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) (hc' : IsCompl (X'.gradedPiece j' 0) (X'.gradedPiece j' 1))
    (hF : X.F.map g = X'.F) (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hbca : IsBaseChangeAlong' g (X.toGradedCartierModuleData j hc) (X'.toGradedCartierModuleData j' hc') (CartierModule.baseChangeEq g hF)) :
    X'.IsHomogeneousVBasis j' (fun i => CartierModule.baseChangeEq g hF (γ i)) := by
  refine ⟨fun i => ?_, ?_⟩
  · exact (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc' i _).mp
      (hbca.2.2.2.2.1 i _ ((FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc i _).mpr (hγ.1 i)))
  · exact isUnit_det_tangent_baseChangeEq _ hF _ hγ.2

theorem nMk_eq_nMk_iff {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j) (a b a' b' : D.M) :
    D.nMk (a, b) = D.nMk (a', b') ↔ ∃ t : D.M, D.verschiebung t = a - a' ∧ -D.varpi t = b - b' := by
  rw [nMk_apply, nMk_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  constructor
  · rintro ⟨m, hm⟩
    rw [nRelMap_apply, Prod.mk_sub_mk, Prod.ext_iff] at hm
    exact ⟨D.ofSigma m, hm.1, by have h__af := hm.2; simp at h__af; exact h__af⟩
  · rintro ⟨t, ht, ht'⟩
    refine ⟨D.toSigma t, ?_⟩
    rw [nRelMap_apply, Prod.mk_sub_mk, Prod.ext_iff]
    exact ⟨ht, by simp at ht' ⊢; exact ht'⟩

theorem nMk_eq_zero_iff {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j) (a b : D.M) :
    D.nMk (a, b) = 0 ↔ ∃ t : D.M, D.verschiebung t = a ∧ -D.varpi t = b := by
  rw [show (0 : D.NMod) = D.nMk (0, 0) from (map_zero D.nMk).symm, nMk_eq_nMk_iff]
  simp only [sub_zero]

theorem nMap_mem_eta {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ m, f (D.verschiebung m) = D'.verschiebung (f m))
    (hP : ∀ m, f (D.varpi m) = D'.varpi (f m))
    (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (L' : D'.M →+ D'.NMod) (hL' : ∀ x : D'.M, L' (D'.verschiebung x) = D'.nMk (D'.varpi x, 0))
    (hLL' : ∀ m, L' (f m) = D.nMap D' f hV hP (L m)) (z : D.NMod) (hz : z ∈ D.eta L hL) :
    D.nMap D' f hV hP z ∈ D'.eta L' hL' := by
  rw [mem_eta_iff] at hz ⊢
  obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective z
  conv_rhs => rw [← hz]
  rw [phi_nMk, map_add, nMap_nMk, nMap_nMk, phi_nMk, hLL', map_zero]

theorem nMap_nMap_eq {B1 B2 B3 : Type} [CommRing B1] [CommRing B2] [CommRing B3]
    {j1 : Zp2 p →+* B1} {j2 : Zp2 p →+* B2} {j3 : Zp2 p →+* B3}
    (D1 : GradedCartierModuleData p B1 j1) (D2 : GradedCartierModuleData p B2 j2)
    (D3 : GradedCartierModuleData p B3 j3)
    (f : D1.M →+ D2.M) (hfV : ∀ x, f (D1.verschiebung x) = D2.verschiebung (f x))
    (hfPi : ∀ x, f (D1.varpi x) = D2.varpi (f x))
    (g : D2.M →+ D3.M) (hgV : ∀ x, g (D2.verschiebung x) = D3.verschiebung (g x))
    (hgPi : ∀ x, g (D2.varpi x) = D3.varpi (g x))
    (k : D1.M →+ D3.M) (hkV : ∀ x, k (D1.verschiebung x) = D3.verschiebung (k x))
    (hkPi : ∀ x, k (D1.varpi x) = D3.varpi (k x))
    (hc : ∀ x, g (f x) = k x) (z : D1.NMod) :
    D2.nMap D3 g hgV hgPi (D1.nMap D2 f hfV hfPi z) = D1.nMap D3 k hkV hkPi z := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D1.nMk_surjective z
  rw [nMap_nMk, nMap_nMk, nMap_nMk, hc, hc]

theorem nMap_eq_zero_of_milnor {B B₀ B₁ B₀₁ : Type} [CommRing B] [CommRing B₀] [CommRing B₁] [CommRing B₀₁]
    {j : Zp2 p →+* B} {j₀ : Zp2 p →+* B₀} {j₁ : Zp2 p →+* B₁} {j₀₁ : Zp2 p →+* B₀₁}
    (D : GradedCartierModuleData p B j) (D₀ : GradedCartierModuleData p B₀ j₀)
    (D₁ : GradedCartierModuleData p B₁ j₁) (D₀₁ : GradedCartierModuleData p B₀₁ j₀₁)
    (f₀ : D.M →+ D₀.M) (f₁ : D.M →+ D₁.M) (g₀ : D₀.M →+ D₀₁.M) (g₁ : D₁.M →+ D₀₁.M)
    (hf₀V : ∀ m, f₀ (D.verschiebung m) = D₀.verschiebung (f₀ m)) (hf₀P : ∀ m, f₀ (D.varpi m) = D₀.varpi (f₀ m))
    (hf₁V : ∀ m, f₁ (D.verschiebung m) = D₁.verschiebung (f₁ m)) (hf₁P : ∀ m, f₁ (D.varpi m) = D₁.varpi (f₁ m))
    (hg₀V : ∀ m, g₀ (D₀.verschiebung m) = D₀₁.verschiebung (g₀ m))
    (hg₁V : ∀ m, g₁ (D₁.verschiebung m) = D₀₁.verschiebung (g₁ m))
    (hsq : ∀ m, g₀ (f₀ m) = g₁ (f₁ m))
    (hinj : ∀ m : D.M, f₀ m = 0 → f₁ m = 0 → m = 0)
    (hglue : ∀ (m₀ : D₀.M) (m₁ : D₁.M), g₀ m₀ = g₁ m₁ → ∃ m : D.M, f₀ m = m₀ ∧ f₁ m = m₁)
    (hV₀₁ : Function.Injective D₀₁.verschiebung)
    (u : D.NMod) (hu₀ : D.nMap D₀ f₀ hf₀V hf₀P u = 0) (hu₁ : D.nMap D₁ f₁ hf₁V hf₁P u = 0) : u = 0 := by
  obtain ⟨⟨c, d⟩, rfl⟩ := D.nMk_surjective u
  rw [nMap_nMk, nMk_eq_zero_iff] at hu₀ hu₁
  obtain ⟨s₀, hs₀, hs₀'⟩ := hu₀
  obtain ⟨s₁, hs₁, hs₁'⟩ := hu₁
  have hgs : g₀ s₀ = g₁ s₁ := by
    apply hV₀₁
    rw [← hg₀V, ← hg₁V, hs₀, hs₁, hsq]
  obtain ⟨s, hs0, hs1⟩ := hglue s₀ s₁ hgs
  have hc : D.verschiebung s = c := by
    rw [← sub_eq_zero]
    apply hinj
    · rw [map_sub, hf₀V, hs0, hs₀, sub_self]
    · rw [map_sub, hf₁V, hs1, hs₁, sub_self]
  have hd : -D.varpi s = d := by
    rw [← sub_eq_zero]
    apply hinj
    · rw [map_sub, map_neg, hf₀P, hs0, hs₀', sub_self]
    · rw [map_sub, map_neg, hf₁P, hs1, hs₁', sub_self]
  rw [← hc, ← hd]
  exact D.nMk_verschiebung_neg_varpi s

theorem baseChangeEq_surjective {R S' : Type} [CommRing R] [Algebra ℤ_[p] R] [CommRing S'] (r : R →+* S')
    (hr : Function.Surjective r) {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm] (Ψ : MvFormalGroup d S') [Ψ.IsComm]
    (h : Φ.map r = Ψ) : Function.Surjective (CartierModule.baseChangeEq (p := p) r h) := by
  subst h
  exact MvFormalGroup.CartierModule.baseChange_surjective_of_surjective p r hr Φ

omit [Fact p.Prime] in

theorem milnor_inj {S : Type} [CommRing S] (J₀ J₁ : Ideal S) (hJ : J₀ ⊓ J₁ = ⊥) (b : S)
    (h₀ : Ideal.Quotient.mk J₀ b = 0) (h₁ : Ideal.Quotient.mk J₁ b = 0) : b = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem] at h₀ h₁
  have : b ∈ J₀ ⊓ J₁ := ⟨h₀, h₁⟩
  rwa [hJ, Ideal.mem_bot] at this

omit [Fact p.Prime] in
theorem milnor_glue {S : Type} [CommRing S] (J₀ J₁ : Ideal S) (b₀ : S ⧸ J₀) (b₁ : S ⧸ J₁)
    (h : Ideal.Quotient.factor (le_sup_left : J₀ ≤ J₀ ⊔ J₁) b₀ = Ideal.Quotient.factor (le_sup_right : J₁ ≤ J₀ ⊔ J₁) b₁) :
    ∃ b : S, Ideal.Quotient.mk J₀ b = b₀ ∧ Ideal.Quotient.mk J₁ b = b₁ := by
  obtain ⟨c₀, rfl⟩ := Ideal.Quotient.mk_surjective b₀
  obtain ⟨c₁, rfl⟩ := Ideal.Quotient.mk_surjective b₁
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.eq, Submodule.mem_sup] at h
  obtain ⟨u, hu, v, hv, huv⟩ := h
  refine ⟨c₀ - u, ?_, ?_⟩
  · rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hu, sub_zero]
  · rw [Ideal.Quotient.eq]
    have : c₀ - u - c₁ = v := by linear_combination (-1 : S) * huv
    rw [this]; exact hv

theorem exists_mem_etaPiece_nsmul_eq {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) (i : Fin 2) (z w : D.NMod)
    (hz : z ∈ D.nPiece i) (hw : w ∈ D.eta L hL.isCartierLMap.map_verschiebung) (n : ℕ) (h : n • w = z) :
    ∃ w' ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung i, n • w' = z := by
  obtain ⟨w₀, hw₀m, w₁, hw₁m, hww⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_mem_etaPiece_add_eq p j D L hL w hw
  have hcmpl := CerednikDrinfeld.GradedCartierModuleData.isCompl_nPiece_zero_one p j D
  have hp0 : n • w₀ ∈ D.nPiece 0 := AddSubgroup.nsmul_mem _ (AddSubgroup.mem_inf.mp hw₀m).2 n
  have hp1 : n • w₁ ∈ D.nPiece 1 := AddSubgroup.nsmul_mem _ (AddSubgroup.mem_inf.mp hw₁m).2 n
  have hsum : n • w₀ + n • w₁ = z := by rw [← nsmul_add, ← hww, h]
  fin_cases i
  · refine ⟨w₀, hw₀m, ?_⟩
    have h1' : n • w₁ ∈ D.nPiece 0 := by
      have : n • w₁ = z - n • w₀ := by rw [← hsum]; abel
      rw [this]; exact sub_mem hz hp0
    have h10 : n • w₁ = 0 := by
      have hmem : n • w₁ ∈ D.nPiece 0 ⊓ D.nPiece 1 := ⟨h1', hp1⟩
      rwa [hcmpl.inf_eq_bot, AddSubgroup.mem_bot] at hmem
    rw [← hsum, h10, add_zero]
  · refine ⟨w₁, hw₁m, ?_⟩
    have h0' : n • w₀ ∈ D.nPiece 1 := by
      have : n • w₀ = z - n • w₁ := by rw [← hsum]; abel
      rw [this]; exact sub_mem hz hp1
    have h00 : n • w₀ = 0 := by
      have hmem : n • w₀ ∈ D.nPiece 0 ⊓ D.nPiece 1 := ⟨hp0, h0'⟩
      rwa [hcmpl.inf_eq_bot, AddSubgroup.mem_bot] at hmem
    rw [← hsum, h00, zero_add]

end MilnorPatchKit

open MilnorPatchKit CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (t : Rigidified p Φ B)
    {S : Type} [CommRing S] [IsNoetherianRing S] (g : B →+* S) (hS : (p : S) = 0)
    (hc : t.IsGradedS ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (i : Fin 2)
    (z : ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS g).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung i)
    (J₀ J₁ : Ideal S) (hJ : J₀ ⊓ J₁ = ⊥)

    (hc₀ : t.IsGradedS ι ψ ((Ideal.Quotient.mk J₀).comp g))
    (L₀ : ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀).M →+ ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
    (hX₀ : (t.XS g).F.map (Ideal.Quotient.mk J₀) = (t.XS ((Ideal.Quotient.mk J₀).comp g)).F)
    (hV₀ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₀ (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hX₀ m))
    (hP₀ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₀ (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hX₀ m))
    (z₀ : ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀).NMod)
    (hz₀ : z₀ ∈ ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung i)
    (hdiv₀ : p • z₀ = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hX₀) hV₀ hP₀ z)

    (hc₁ : t.IsGradedS ι ψ ((Ideal.Quotient.mk J₁).comp g))
    (L₁ : ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁).M →+ ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁).NMod) (hL₁ : ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁).IsCanonicalLMap L₁)
    (hX₁ : (t.XS g).F.map (Ideal.Quotient.mk J₁) = (t.XS ((Ideal.Quotient.mk J₁).comp g)).F)
    (hV₁ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₁ (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hX₁ m))
    (hP₁ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₁ (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hX₁ m))
    (z₁ : ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁).NMod)
    (hz₁ : z₁ ∈ ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁).etaPiece L₁ hL₁.isCartierLMap.map_verschiebung i)
    (hdiv₁ : p • z₁ = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁) (MvFormalGroup.CartierModule.baseChangeEq _ hX₁) hV₁ hP₁ z) :
    ∃ w ∈ ((t.XS g).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung i, p • w = z := by
  classical
  letI algS : Algebra ℤ_[p] S := (g.comp (algebraMap ℤ_[p] B)).toAlgebra
  letI algS₀ : Algebra ℤ_[p] (S ⧸ J₀) := ((Ideal.Quotient.mk J₀).comp (g.comp (algebraMap ℤ_[p] B))).toAlgebra
  letI algS₁ : Algebra ℤ_[p] (S ⧸ J₁) := ((Ideal.Quotient.mk J₁).comp (g.comp (algebraMap ℤ_[p] B))).toAlgebra
  letI algS₀₁ : Algebra ℤ_[p] (S ⧸ (J₀ ⊔ J₁)) := ((Ideal.Quotient.mk (J₀ ⊔ J₁)).comp (g.comp (algebraMap ℤ_[p] B))).toAlgebra

  have hpS : IsNilpotent ((p : ℕ) : S) := ⟨1, by rw [pow_one]; exact hS⟩
  have hpQ : ∀ J : Ideal S, IsNilpotent ((p : ℕ) : S ⧸ J) := fun J =>
    ⟨1, by rw [pow_one, ← map_natCast (Ideal.Quotient.mk J) p, hS, map_zero]⟩

  obtain ⟨q, hq⟩ : ∃ q : S →+* S ⧸ (J₀ ⊔ J₁), q = Ideal.Quotient.mk (J₀ ⊔ J₁) := ⟨_, rfl⟩
  obtain ⟨r₀, hr₀def⟩ : ∃ r : S ⧸ J₀ →+* S ⧸ (J₀ ⊔ J₁), r = Ideal.Quotient.factor (le_sup_left : J₀ ≤ J₀ ⊔ J₁) := ⟨_, rfl⟩
  obtain ⟨r₁, hr₁def⟩ : ∃ r : S ⧸ J₁ →+* S ⧸ (J₀ ⊔ J₁), r = Ideal.Quotient.factor (le_sup_right : J₁ ≤ J₀ ⊔ J₁) := ⟨_, rfl⟩
  have hr₀ : r₀.comp (Ideal.Quotient.mk J₀) = q := by rw [hr₀def, hq]; exact Ideal.Quotient.factor_comp_mk _
  have hr₁ : r₁.comp (Ideal.Quotient.mk J₁) = q := by rw [hr₁def, hq]; exact Ideal.Quotient.factor_comp_mk _
  have hsq_ring : r₀.comp (Ideal.Quotient.mk J₀) = r₁.comp (Ideal.Quotient.mk J₁) := hr₀.trans hr₁.symm
  have hr₀s : Function.Surjective r₀ := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective (I := J₀ ⊔ J₁) y
    exact ⟨Ideal.Quotient.mk J₀ s, by rw [← hq, ← hr₀]; rfl⟩
  have hc₀₁ : t.IsGradedS ι ψ (q.comp g) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hpQ _) _

  have hXq : (t.XS g).F.map q = (t.XS (q.comp g)).F := by
    show (t.X.F.map g).map q = t.X.F.map (q.comp g)
    rw [MvFormalGroup.map_map_ringHom]
  have hXr₀ : (t.XS ((Ideal.Quotient.mk J₀).comp g)).F.map r₀ = (t.XS (q.comp g)).F := by
    show (t.X.F.map ((Ideal.Quotient.mk J₀).comp g)).map r₀ = t.X.F.map (q.comp g)
    rw [MvFormalGroup.map_map_ringHom, ← RingHom.comp_assoc, hr₀]
  have hXr₁ : (t.XS ((Ideal.Quotient.mk J₁).comp g)).F.map r₁ = (t.XS (q.comp g)).F := by
    show (t.X.F.map ((Ideal.Quotient.mk J₁).comp g)).map r₁ = t.X.F.map (q.comp g)
    rw [MvFormalGroup.map_map_ringHom, ← RingHom.comp_assoc, hr₁]

  obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL.exists_lift
  obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
  have hγ : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) (fun k => fl (γl k)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData p _ _ hc _ hγf

  have hj₀ : (Ideal.Quotient.mk J₀).comp (Rigidified.jS ι ψ g) = Rigidified.jS ι ψ ((Ideal.Quotient.mk J₀).comp g) :=
    RingHom.ext fun _ => rfl
  have hj₁ : (Ideal.Quotient.mk J₁).comp (Rigidified.jS ι ψ g) = Rigidified.jS ι ψ ((Ideal.Quotient.mk J₁).comp g) :=
    RingHom.ext fun _ => rfl
  have hjq : q.comp (Rigidified.jS ι ψ g) = Rigidified.jS ι ψ (q.comp g) := RingHom.ext fun _ => rfl
  have hXm₀ : (t.XS g).map (Ideal.Quotient.mk J₀) = t.XS ((Ideal.Quotient.mk J₀).comp g) := by
    rw [FormalODModule.map_map]
  have hXm₁ : (t.XS g).map (Ideal.Quotient.mk J₁) = t.XS ((Ideal.Quotient.mk J₁).comp g) := by
    rw [FormalODModule.map_map]
  have hXmq : (t.XS g).map q = t.XS (q.comp g) := by
    rw [FormalODModule.map_map]
  have hbca₀ : IsBaseChangeAlong' (Ideal.Quotient.mk J₀) ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc)
      ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((Ideal.Quotient.mk J₀).comp g)) hc₀)
      (MvFormalGroup.CartierModule.baseChangeEq _ hX₀) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXm₀ _ hj₀ hc₀ hX₀
  have hbca₁ : IsBaseChangeAlong' (Ideal.Quotient.mk J₁) ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc)
      ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((Ideal.Quotient.mk J₁).comp g)) hc₁)
      (MvFormalGroup.CartierModule.baseChangeEq _ hX₁) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXm₁ _ hj₁ hc₁ hX₁
  have hbcaq : IsBaseChangeAlong' q ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc)
      ((t.XS (q.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (q.comp g)) hc₀₁)
      (MvFormalGroup.CartierModule.baseChangeEq _ hXq) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXmq _ hjq hc₀₁ hXq
  have hγ₀ := isHomogeneousVBasis_push (Ideal.Quotient.mk J₀) (t.XS g) (t.XS ((Ideal.Quotient.mk J₀).comp g)) hc hc₀ hX₀ _ hγ hbca₀
  have hγ₁ := isHomogeneousVBasis_push (Ideal.Quotient.mk J₁) (t.XS g) (t.XS ((Ideal.Quotient.mk J₁).comp g)) hc hc₁ hX₁ _ hγ hbca₁
  have hγ₀₁ := isHomogeneousVBasis_push q (t.XS g) (t.XS (q.comp g)) hc hc₀₁ hXq _ hγ hbcaq
  have hjr₀ : r₀.comp (Rigidified.jS ι ψ ((Ideal.Quotient.mk J₀).comp g)) = Rigidified.jS ι ψ (q.comp g) := by
    show r₀.comp (((Ideal.Quotient.mk J₀).comp g).comp (structureMap ι ψ)) = (q.comp g).comp (structureMap ι ψ)
    rw [← hr₀]; rfl
  have hjr₁ : r₁.comp (Rigidified.jS ι ψ ((Ideal.Quotient.mk J₁).comp g)) = Rigidified.jS ι ψ (q.comp g) := by
    show r₁.comp (((Ideal.Quotient.mk J₁).comp g).comp (structureMap ι ψ)) = (q.comp g).comp (structureMap ι ψ)
    rw [← hr₁]; rfl
  have hXmr₀ : (t.XS ((Ideal.Quotient.mk J₀).comp g)).map r₀ = t.XS (q.comp g) := by
    rw [Rigidified.XS, Rigidified.XS, FormalODModule.map_map, ← RingHom.comp_assoc, hr₀]
  have hXmr₁ : (t.XS ((Ideal.Quotient.mk J₁).comp g)).map r₁ = t.XS (q.comp g) := by
    rw [Rigidified.XS, Rigidified.XS, FormalODModule.map_map, ← RingHom.comp_assoc, hr₁]
  have hbcar₀ : IsBaseChangeAlong' r₀
      ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((Ideal.Quotient.mk J₀).comp g)) hc₀)
      ((t.XS (q.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (q.comp g)) hc₀₁)
      (MvFormalGroup.CartierModule.baseChangeEq _ hXr₀) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ₀ hc₀ _ hXmr₀ _ hjr₀ hc₀₁ hXr₀
  have hbcar₁ : IsBaseChangeAlong' r₁
      ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((Ideal.Quotient.mk J₁).comp g)) hc₁)
      ((t.XS (q.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (q.comp g)) hc₀₁)
      (MvFormalGroup.CartierModule.baseChangeEq _ hXr₁) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ₁ hc₁ _ hXmr₁ _ hjr₁ hc₀₁ hXr₁

  have hD := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ hc).2
  have hD₀ := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ₀ hc₀).2
  have hD₁ := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ₁ hc₁).2
  have hD₀₁ := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ₀₁ hc₀₁).2
  obtain ⟨L₀₁, hL₀₁⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (Rigidified.jS ι ψ (q.comp g)) (isHausdorff_of_isNilpotent (hpQ _)) _ _ hγ₀₁ hc₀₁

  have hLL₀ := natL_of_eq _ _ hpS (hpQ J₀) _ hD _ hj₀ _ hD₀ _ hbca₀ L hL L₀ hL₀
  have hLL₁ := natL_of_eq _ _ hpS (hpQ J₁) _ hD _ hj₁ _ hD₁ _ hbca₁ L hL L₁ hL₁
  have hLr₀ := natL_of_eq _ _ (hpQ J₀) (hpQ _) _ hD₀ _ hjr₀ _ hD₀₁ _ hbcar₀ L₀ hL₀ L₀₁ hL₀₁
  have hLr₁ := natL_of_eq _ _ (hpQ J₁) (hpQ _) _ hD₁ _ hjr₁ _ hD₀₁ _ hbcar₁ L₁ hL₁ L₀₁ hL₀₁

  obtain ⟨hMinj, hMglue⟩ := MvFormalGroup.CartierModule.exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor p
    (Ideal.Quotient.mk J₀) (Ideal.Quotient.mk J₁) r₀ r₁ hsq_ring (milnor_inj J₀ J₁ hJ)
    (fun b₀ b₁ h => milnor_glue J₀ J₁ b₀ b₁ (by rw [← hr₀def, ← hr₁def]; exact h))
    (t.XS g).F (t.XS ((Ideal.Quotient.mk J₀).comp g)).F hX₀ (t.XS ((Ideal.Quotient.mk J₁).comp g)).F hX₁
    (t.XS (q.comp g)).F hXr₀ hXr₁
  have hsqM : ∀ m : MvFormalGroup.CartierModule p (t.XS g).F, MvFormalGroup.CartierModule.baseChangeEq r₀ hXr₀ (MvFormalGroup.CartierModule.baseChangeEq _ hX₀ m) =
      MvFormalGroup.CartierModule.baseChangeEq r₁ hXr₁ (MvFormalGroup.CartierModule.baseChangeEq _ hX₁ m) := by
    intro m
    apply MvFormalGroup.CartierModule.ext
    funext k
    show MvPowerSeries.map r₀ (MvPowerSeries.map (Ideal.Quotient.mk J₀) (m.toPowerSeries k)) =
      MvPowerSeries.map r₁ (MvPowerSeries.map (Ideal.Quotient.mk J₁) (m.toPowerSeries k))
    rw [MvPowerSeries.map_map, MvPowerSeries.map_map, hsq_ring]
  have hk₀ : ∀ m : MvFormalGroup.CartierModule p (t.XS g).F, MvFormalGroup.CartierModule.baseChangeEq r₀ hXr₀ (MvFormalGroup.CartierModule.baseChangeEq _ hX₀ m) =
      MvFormalGroup.CartierModule.baseChangeEq q hXq m := by
    intro m
    apply MvFormalGroup.CartierModule.ext
    funext k
    show MvPowerSeries.map r₀ (MvPowerSeries.map (Ideal.Quotient.mk J₀) (m.toPowerSeries k)) = MvPowerSeries.map q (m.toPowerSeries k)
    rw [MvPowerSeries.map_map, hr₀]
  have hk₁ : ∀ m : MvFormalGroup.CartierModule p (t.XS g).F, MvFormalGroup.CartierModule.baseChangeEq r₁ hXr₁ (MvFormalGroup.CartierModule.baseChangeEq _ hX₁ m) =
      MvFormalGroup.CartierModule.baseChangeEq q hXq m := by
    intro m
    apply MvFormalGroup.CartierModule.ext
    funext k
    show MvPowerSeries.map r₁ (MvPowerSeries.map (Ideal.Quotient.mk J₁) (m.toPowerSeries k)) = MvPowerSeries.map q (m.toPowerSeries k)
    rw [MvPowerSeries.map_map, hr₁]

  have hg₀s : Function.Surjective (MvFormalGroup.CartierModule.baseChangeEq (p := p) r₀ hXr₀) :=
    baseChangeEq_surjective r₀ hr₀s _ _ hXr₀
  obtain ⟨γ', -, hγ'⟩ := hbcaq.2.2.2.2.2
  have hV₀₁ := hγ'.verschiebung_injective

  have hz₀e := (AddSubgroup.mem_inf.mp hz₀).1
  have hz₁e := (AddSubgroup.mem_inf.mp hz₁).1
  have hdiv₀' : p • z₀ = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((Ideal.Quotient.mk J₀).comp g)) hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hX₀) hbca₀.2.2.1 hbca₀.2.2.2.1 z := hdiv₀
  have hdiv₁' : p • z₁ = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((Ideal.Quotient.mk J₁).comp g)) hc₁) (MvFormalGroup.CartierModule.baseChangeEq _ hX₁) hbca₁.2.2.1 hbca₁.2.2.2.1 z := hdiv₁
  have hy₀ := nMap_mem_eta _ _ _ hbcar₀.2.2.1 hbcar₀.2.2.2.1 L₀ hL₀.isCartierLMap.map_verschiebung L₀₁ hL₀₁.isCartierLMap.map_verschiebung hLr₀ z₀ hz₀e
  have hy₁ := nMap_mem_eta _ _ _ hbcar₁.2.2.1 hbcar₁.2.2.2.1 L₁ hL₁.isCartierLMap.map_verschiebung L₀₁ hL₀₁.isCartierLMap.map_verschiebung hLr₁ z₁ hz₁e
  have hpy : p • ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((Ideal.Quotient.mk J₀).comp g)) hc₀).nMap ((t.XS (q.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (q.comp g)) hc₀₁) (MvFormalGroup.CartierModule.baseChangeEq r₀ hXr₀) hbcar₀.2.2.1 hbcar₀.2.2.2.1 z₀ =
      p • ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((Ideal.Quotient.mk J₁).comp g)) hc₁).nMap ((t.XS (q.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (q.comp g)) hc₀₁) (MvFormalGroup.CartierModule.baseChangeEq r₁ hXr₁) hbcar₁.2.2.1 hbcar₁.2.2.2.1 z₁ := by
    rw [← map_nsmul, ← map_nsmul, hdiv₀', hdiv₁',
      nMap_nMap_eq _ _ _ _ hbca₀.2.2.1 hbca₀.2.2.2.1 _ hbcar₀.2.2.1 hbcar₀.2.2.2.1 _ hbcaq.2.2.1 hbcaq.2.2.2.1 hk₀,
      nMap_nMap_eq _ _ _ _ hbca₁.2.2.1 hbca₁.2.2.2.1 _ hbcar₁.2.2.1 hbcar₁.2.2.2.1 _ hbcaq.2.2.1 hbcaq.2.2.2.1 hk₁]
  have hcompat : ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((Ideal.Quotient.mk J₀).comp g)) hc₀).nMap ((t.XS (q.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (q.comp g)) hc₀₁) (MvFormalGroup.CartierModule.baseChangeEq r₀ hXr₀) hbcar₀.2.2.1 hbcar₀.2.2.2.1 z₀ =
      ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((Ideal.Quotient.mk J₁).comp g)) hc₁).nMap ((t.XS (q.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (q.comp g)) hc₀₁) (MvFormalGroup.CartierModule.baseChangeEq r₁ hXr₁) hbcar₁.2.2.1 hbcar₁.2.2.2.1 z₁ := by
    rw [← sub_eq_zero]
    exact CerednikDrinfeld.FormalODModule.eq_zero_of_nsmul_eq_zero_of_mem_eta p (hpQ _) (Rigidified.jS ι ψ (q.comp g))
      (t.XS (q.comp g)) _ hγ₀₁ hc₀₁ L₀₁ hL₀₁ _ (sub_mem hy₀ hy₁) (by rw [nsmul_sub, hpy, sub_self])

  obtain ⟨w, hw, hw₀, hw₁⟩ := CerednikDrinfeld.GradedCartierModuleData.exists_mem_eta_nMap_eq_of_nMap_eq_nMap p
    ((t.XS g).toGradedCartierModuleData _ hc) ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀)
    ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁) ((t.XS (q.comp g)).toGradedCartierModuleData _ hc₀₁)
    (MvFormalGroup.CartierModule.baseChangeEq _ hX₀) (MvFormalGroup.CartierModule.baseChangeEq _ hX₁)
    (MvFormalGroup.CartierModule.baseChangeEq r₀ hXr₀) (MvFormalGroup.CartierModule.baseChangeEq r₁ hXr₁)
    hbca₀.2.2.1 hbca₀.2.2.2.1 hbca₁.2.2.1 hbca₁.2.2.2.1 hbcar₀.2.2.1 hbcar₀.2.2.2.1 hbcar₁.2.2.1 hbcar₁.2.2.2.1
    hsqM hMinj hMglue hg₀s hV₀₁ L hL.isCartierLMap L₀ hL₀.isCartierLMap L₁ hL₁.isCartierLMap hLL₀ hLL₁
    z₀ hz₀e z₁ hz₁e hcompat

  have hpw : p • w = z := by
    rw [← sub_eq_zero]
    exact nMap_eq_zero_of_milnor _ _ _ _ _ _ _ _ hbca₀.2.2.1 hbca₀.2.2.2.1 hbca₁.2.2.1 hbca₁.2.2.2.1 hbcar₀.2.2.1 hbcar₁.2.2.1
      hsqM hMinj hMglue hV₀₁ _ (by rw [map_sub, map_nsmul, hw₀, hdiv₀', sub_self]) (by rw [map_sub, map_nsmul, hw₁, hdiv₁', sub_self])

  exact exists_mem_etaPiece_nsmul_eq _ L hL i z w (AddSubgroup.mem_inf.mp hz).2 hw p hpw

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_mem_etaPiece_smul_eq_of_smul_eq_nMap_quotient_of_inf_eq_bot
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_mem_etaPiece_smul_eq_of_smul_eq_nMap_quotient_of_inf_eq_bot (solution)
