-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_smul_eq_nMap_nMap_localization_localization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d5537705-7de6-56e7-bc78-01c5926cc955

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
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_mem_etaPiece_add_eq
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_isCompl_nPiece_zero_one
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_bijective_eta_map_of_surjective_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_smul_eq_nMap_nMap_localization_localization
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace LocComposeKit

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

theorem redInv_of_eq {B B' : Type} [CommRing B] [CommRing B'] (j : Zp2 p →+* B) (φ : B →+* B')
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ))
    (hIp : ∃ b : ℕ, ∀ x ∈ RingHom.ker φ, (p : B) ^ b * x = 0)
    (D : GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (j' : Zp2 p →+* B') (hj : φ.comp j = j')
    (D' : GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : IsBaseChangeAlong' φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (L' : D'.M →+ D'.NMod) (hL' : D'.IsCanonicalLMap L')
    (hLL' : ∀ x : D.M, L' (f x) = D.nMap D' f hf.2.2.1 hf.2.2.2.1 (L x)) :
    Set.BijOn (D.nMap D' f hf.2.2.1 hf.2.2.2.1)
      (D.eta L hL.isCartierLMap.map_verschiebung : Set D.NMod)
      (D'.eta L' hL'.isCartierLMap.map_verschiebung : Set D'.NMod) := by
  subst hj
  exact CerednikDrinfeld.GradedCartierModuleData.bijective_eta_map_of_surjective_of_isNilpotent p j φ hφ hI hIp
    D hD D' hD' f hf L hL L' hL' hLL'

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

theorem nMap_mem_nPiece {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ m, f (D.verschiebung m) = D'.verschiebung (f m))
    (hP : ∀ m, f (D.varpi m) = D'.varpi (f m))
    (hf : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i)
    (i : Fin 2) (z : D.NMod) (hz : z ∈ D.nPiece i) : D.nMap D' f hV hP z ∈ D'.nPiece i := by
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := hz
  refine ⟨(f a, f b), ⟨hf i a hab.1, hf i b hab.2⟩, ?_⟩
  show D'.nMk (f a, f b) = D.nMap D' f hV hP (D.nMk (a, b))
  rw [nMap_nMk]

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

end LocComposeKit

open LocComposeKit CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    {S : Type} [CommRing S] [IsNoetherianRing S] (g : B →+* S) (hS : (p : S) = 0)
    (hc : t.IsGradedS ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (j : Fin 2)
    (z : ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS g).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung j)
    (x : PrimeSpectrum S)
    (f₀ : S) (hf₀ : f₀ ∉ x.asIdeal)
    (hc₁ : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀)).comp g))
    (hX₁ : (t.XS g).F.map (algebraMap S (Localization.Away f₀)) = (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F)
    (hV₁ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₁ (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₁).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hX₁ m))
    (hP₁ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₁ (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₁).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hX₁ m))
    (x₁ : PrimeSpectrum (Localization.Away f₀)) (hx₁ : x₁.asIdeal.comap (algebraMap S (Localization.Away f₀)) = x.asIdeal)
    (f₁ : (Localization.Away f₀)) (hf₁ : f₁ ∉ x₁.asIdeal)
    (hc₂ : t.IsGradedS ι ψ ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g)))
    (L₂ : ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂).M →+ ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂).NMod) (hL₂ : ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂).IsCanonicalLMap L₂)
    (hX₂ : (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F.map (algebraMap (Localization.Away f₀) (Localization.Away f₁)) = (t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).F)
    (hV₂ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₂ (((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₁).verschiebung m) =
      ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hX₂ m))
    (hP₂ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₂ (((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₁).varpi m) =
      ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hX₂ m))
    (z₂ : ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂).NMod) (hz₂ : z₂ ∈ ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂).etaPiece L₂ hL₂.isCartierLMap.map_verschiebung j)
    (heq : p • z₂ = ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₁).nMap ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂) (MvFormalGroup.CartierModule.baseChangeEq _ hX₂) hV₂ hP₂
      (((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₁) (MvFormalGroup.CartierModule.baseChangeEq _ hX₁) hV₁ hP₁ z)) :
    ∃ (f₀ : S) (_ : f₀ ∉ x.asIdeal) (hc₀ : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀)).comp g))
      (L₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).M →+ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
      (hXr : (t.XS g).F.map (algebraMap S (Localization.Away f₀)) = (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F)
      (hrV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (hrPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (z₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod),
      z₀ ∈ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung j ∧
        p • z₀ = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXr) hrV hrPi z := by
  classical
  have hpS : IsNilpotent ((p : ℕ) : S) := ⟨1, by rw [pow_one]; exact hS⟩
  have hpA₀ : IsNilpotent ((p : ℕ) : Localization.Away f₀) := by
    simpa only [map_natCast] using hpS.map (algebraMap S (Localization.Away f₀))
  have hpT : IsNilpotent ((p : ℕ) : Localization.Away f₁) := by
    simpa only [map_natCast] using hpA₀.map (algebraMap (Localization.Away f₀) (Localization.Away f₁))

  obtain ⟨k, n, hkn⟩ := IsLocalization.Away.surj f₀ f₁

  have hn_x : n ∉ x.asIdeal := by
    intro hnx
    have h1 : algebraMap S (Localization.Away f₀) n ∈ x₁.asIdeal := by
      rw [← hx₁] at hnx; exact hnx
    have h2 : f₁ * algebraMap S (Localization.Away f₀) f₀ ^ k ∈ x₁.asIdeal := by
      rw [hkn]; exact h1
    rcases x₁.isPrime.mem_or_mem h2 with h3 | h3
    · exact hf₁ h3
    · have h4 : f₀ ^ k ∈ x.asIdeal := by
        rw [← hx₁, Ideal.mem_comap, map_pow]; exact h3
      exact hf₀ (x.isPrime.mem_of_pow_mem k h4)
  have hf_x : f₀ * n ∉ x.asIdeal := fun h => (x.isPrime.mem_or_mem h).elim hf₀ hn_x

  haveI hAw : IsLocalization.Away (f₀ * n) (Localization.Away f₁) :=
    IsLocalization.Away.mul_of_associated f₀ n f₁ (by
      obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away f₀) f₀ k
      exact Associated.symm ⟨u, by rw [hu]; exact hkn⟩)
  obtain ⟨θ, hθ, hθsurj, hθinj⟩ : ∃ θ : Localization.Away (f₀ * n) →+* Localization.Away f₁,
      θ.comp (algebraMap S (Localization.Away (f₀ * n))) = algebraMap S (Localization.Away f₁) ∧
      Function.Surjective θ ∧ Function.Injective θ := by
    let e := IsLocalization.algEquiv (Submonoid.powers (f₀ * n)) (Localization.Away (f₀ * n)) (Localization.Away f₁)
    exact ⟨(e.toAlgHom : Localization.Away (f₀ * n) →+* Localization.Away f₁), e.toAlgHom.comp_algebraMap,
      e.surjective, e.injective⟩
  have hθ' : θ.comp (algebraMap S (Localization.Away (f₀ * n))) =
      (algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp (algebraMap S (Localization.Away f₀)) := by
    rw [hθ]; exact IsScalarTower.algebraMap_eq S (Localization.Away f₀) (Localization.Away f₁)
  have hθg : θ.comp ((algebraMap S (Localization.Away (f₀ * n))).comp g) =
      (algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g) := by
    rw [← RingHom.comp_assoc, hθ', RingHom.comp_assoc]
  have hker : RingHom.ker θ = ⊥ := (RingHom.injective_iff_ker_eq_bot θ).mp hθinj
  have hkerNil : IsNilpotent (RingHom.ker θ) := by
    rw [hker]; exact ⟨1, by rw [pow_one, Ideal.zero_eq_bot]⟩
  have hkerp : ∃ b : ℕ, ∀ r ∈ RingHom.ker θ, ((p : ℕ) : Localization.Away (f₀ * n)) ^ b * r = 0 :=
    ⟨0, fun r hr => by rw [hker, Ideal.mem_bot] at hr; rw [hr, mul_zero]⟩

  have hpR : IsNilpotent ((p : ℕ) : Localization.Away (f₀ * n)) := by
    simpa only [map_natCast] using hpS.map (algebraMap S (Localization.Away (f₀ * n)))
  have hcR : t.IsGradedS ι ψ ((algebraMap S (Localization.Away (f₀ * n))).comp g) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpR _

  have hXm_res : (t.XS g).map (algebraMap S (Localization.Away (f₀ * n))) = t.XS ((algebraMap S (Localization.Away (f₀ * n))).comp g) := by
    rw [Rigidified.XS, Rigidified.XS, FormalODModule.map_map]
  have hXres : (t.XS g).F.map (algebraMap S (Localization.Away (f₀ * n))) = (t.XS ((algebraMap S (Localization.Away (f₀ * n))).comp g)).F :=
    congrArg FormalODModule.F hXm_res
  have hXm_θ : (t.XS ((algebraMap S (Localization.Away (f₀ * n))).comp g)).map θ =
      t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g)) := by
    rw [Rigidified.XS, Rigidified.XS, FormalODModule.map_map, hθg]
  have hXθ : (t.XS ((algebraMap S (Localization.Away (f₀ * n))).comp g)).F.map θ =
      (t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).F :=
    congrArg FormalODModule.F hXm_θ
  have hj_res : (algebraMap S (Localization.Away (f₀ * n))).comp (Rigidified.jS ι ψ g) = Rigidified.jS ι ψ ((algebraMap S (Localization.Away (f₀ * n))).comp g) := rfl
  have hj_θ : θ.comp (Rigidified.jS ι ψ ((algebraMap S (Localization.Away (f₀ * n))).comp g)) =
      Rigidified.jS ι ψ ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g)) := by
    show θ.comp (((algebraMap S (Localization.Away (f₀ * n))).comp g).comp (structureMap ι ψ)) =
      ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g)).comp (structureMap ι ψ)
    rw [← RingHom.comp_assoc, hθg]

  letI : Algebra ℤ_[p] S := (g.comp (algebraMap ℤ_[p] B)).toAlgebra
  obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL.exists_lift
  obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
  have hγ : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) (fun k => fl (γl k)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData p _ _ hc _ hγf
  have hbca_res : IsBaseChangeAlong' (algebraMap S (Localization.Away (f₀ * n))) ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t.XS ((algebraMap S (Localization.Away (f₀ * n))).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away (f₀ * n))).comp g)) hcR) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXm_res _ hj_res hcR hXres
  have hγR := isHomogeneousVBasis_push (algebraMap S (Localization.Away (f₀ * n))) (t.XS g) (t.XS ((algebraMap S (Localization.Away (f₀ * n))).comp g)) hc hcR hXres _ hγ hbca_res
  have hbca_θ : IsBaseChangeAlong' θ ((t.XS ((algebraMap S (Localization.Away (f₀ * n))).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away (f₀ * n))).comp g)) hcR) ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))) hc₂) (MvFormalGroup.CartierModule.baseChangeEq _ hXθ) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγR hcR _ hXm_θ _ hj_θ hc₂ hXθ
  have hγT := isHomogeneousVBasis_push θ (t.XS ((algebraMap S (Localization.Away (f₀ * n))).comp g)) (t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))) hcR hc₂ hXθ _ hγR hbca_θ

  have hD := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ hc).2
  have hDR := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγR hcR).2
  have hDT := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγT hc₂).2
  obtain ⟨LR, hLR⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (Rigidified.jS ι ψ ((algebraMap S (Localization.Away (f₀ * n))).comp g)) (isHausdorff_of_isNilpotent hpR) _ _ hγR hcR
  have hLL_res := natL_of_eq _ _ hpS hpR _ hD _ hj_res _ hDR _ hbca_res L hL LR hLR
  have hLL_θ := natL_of_eq _ _ hpR hpT _ hDR _ hj_θ _ hDT _ hbca_θ LR hLR L₂ hL₂

  have hbij := redInv_of_eq _ _ hθsurj hkerNil hkerp _ hDR _ hj_θ _ hDT _ hbca_θ LR hLR L₂ hL₂ hLL_θ

  have hzE := (AddSubgroup.mem_inf.mp hz).1
  have hzP := (AddSubgroup.mem_inf.mp hz).2
  have hNz_eta := nMap_mem_eta _ _ _ hbca_res.2.2.1 hbca_res.2.2.2.1 L hL.isCartierLMap.map_verschiebung LR hLR.isCartierLMap.map_verschiebung hLL_res z hzE
  have hNz_piece := nMap_mem_nPiece _ _ _ hbca_res.2.2.1 hbca_res.2.2.2.1 hbca_res.2.2.2.2.1 j z hzP

  have hz₂E := (AddSubgroup.mem_inf.mp hz₂).1
  obtain ⟨w, hw, hNw⟩ := hbij.surjOn hz₂E

  have hsq : ∀ m : MvFormalGroup.CartierModule p (t.XS g).F,
      MvFormalGroup.CartierModule.baseChangeEq θ hXθ (MvFormalGroup.CartierModule.baseChangeEq _ hXres m) =
      MvFormalGroup.CartierModule.baseChangeEq _ hX₂ (MvFormalGroup.CartierModule.baseChangeEq _ hX₁ m) := by
    intro m
    apply MvFormalGroup.CartierModule.ext
    funext k
    show MvPowerSeries.map θ (MvPowerSeries.map (algebraMap S (Localization.Away (f₀ * n))) (m.toPowerSeries k)) =
      MvPowerSeries.map (algebraMap (Localization.Away f₀) (Localization.Away f₁)) (MvPowerSeries.map (algebraMap S (Localization.Away f₀)) (m.toPowerSeries k))
    rw [MvPowerSeries.map_map, MvPowerSeries.map_map, hθ']

  have hkV : ∀ m, ((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).verschiebung m) = ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))) hc₂).verschiebung (((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) m) := fun m =>
    (congrArg (MvFormalGroup.CartierModule.baseChangeEq θ hXθ) (hbca_res.2.2.1 m)).trans (hbca_θ.2.2.1 _)
  have hkP : ∀ m, ((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).varpi m) = ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))) hc₂).varpi (((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) m) := fun m =>
    (congrArg (MvFormalGroup.CartierModule.baseChangeEq θ hXθ) (hbca_res.2.2.2.1 m)).trans (hbca_θ.2.2.2.1 _)
  have heq' : p • z₂ = ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) hc₁).nMap ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))) hc₂) (MvFormalGroup.CartierModule.baseChangeEq _ hX₂) hV₂ hP₂
      (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) hc₁) (MvFormalGroup.CartierModule.baseChangeEq _ hX₁) hV₁ hP₁ z) := heq
  have e1 : ((t.XS ((algebraMap S (Localization.Away (f₀ * n))).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away (f₀ * n))).comp g)) hcR).nMap ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))) hc₂) (MvFormalGroup.CartierModule.baseChangeEq θ hXθ) hbca_θ.2.2.1 hbca_θ.2.2.2.1
        (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS ((algebraMap S (Localization.Away (f₀ * n))).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away (f₀ * n))).comp g)) hcR) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) hbca_res.2.2.1 hbca_res.2.2.2.1 z) =
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))) hc₂) ((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) hkV hkP z :=
    nMap_nMap_eq ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t.XS ((algebraMap S (Localization.Away (f₀ * n))).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away (f₀ * n))).comp g)) hcR) ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))) hc₂) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) hbca_res.2.2.1 hbca_res.2.2.2.1
      (MvFormalGroup.CartierModule.baseChangeEq θ hXθ) hbca_θ.2.2.1 hbca_θ.2.2.2.1 ((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) hkV hkP (fun _ => rfl) z
  have e2 : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) hc₁).nMap ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))) hc₂) (MvFormalGroup.CartierModule.baseChangeEq _ hX₂) hV₂ hP₂
        (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) hc₁) (MvFormalGroup.CartierModule.baseChangeEq _ hX₁) hV₁ hP₁ z) =
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))) hc₂) ((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) hkV hkP z :=
    nMap_nMap_eq ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) hc₁) ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))) hc₂) (MvFormalGroup.CartierModule.baseChangeEq _ hX₁) hV₁ hP₁
      (MvFormalGroup.CartierModule.baseChangeEq _ hX₂) hV₂ hP₂ ((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) hkV hkP (fun m => (hsq m).symm) z
  have hkey : ((t.XS ((algebraMap S (Localization.Away (f₀ * n))).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away (f₀ * n))).comp g)) hcR).nMap ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))) hc₂) (MvFormalGroup.CartierModule.baseChangeEq θ hXθ) hbca_θ.2.2.1 hbca_θ.2.2.2.1 (p • w) =
      ((t.XS ((algebraMap S (Localization.Away (f₀ * n))).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away (f₀ * n))).comp g)) hcR).nMap ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))) hc₂) (MvFormalGroup.CartierModule.baseChangeEq θ hXθ) hbca_θ.2.2.1 hbca_θ.2.2.2.1
        (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS ((algebraMap S (Localization.Away (f₀ * n))).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away (f₀ * n))).comp g)) hcR) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) hbca_res.2.2.1 hbca_res.2.2.2.1 z) := by
    rw [map_nsmul, hNw]
    exact heq'.trans (e2.trans e1.symm)
  have hpw : p • w = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS ((algebraMap S (Localization.Away (f₀ * n))).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away (f₀ * n))).comp g)) hcR) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) hbca_res.2.2.1 hbca_res.2.2.2.1 z :=
    hbij.injOn (AddSubgroup.nsmul_mem _ hw p) hNz_eta hkey

  obtain ⟨w', hw', hpw'⟩ := exists_mem_etaPiece_nsmul_eq _ LR hLR j _ w hNz_piece hw p hpw
  exact ⟨f₀ * n, hf_x, hcR, LR, hLR, hXres, hbca_res.2.2.1, hbca_res.2.2.2.1, w', hw', hpw'⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_smul_eq_nMap_nMap_localization_localization
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_smul_eq_nMap_nMap_localization_localization (solution)
