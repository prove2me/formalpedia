-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_nMap_of_map_eq_zero_of_forall_mul_eq_zero_of_nMap_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/3e22671e-f11f-5980-9e77-a6942d85b584

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
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_comp_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_teichmuller_smul_add_verschiebung
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_nMap_of_map_eq_zero_of_forall_mul_eq_zero_of_nMap_eq_smul
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace SdncPushKit

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

theorem nMap_mem_etaPiece {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ m, f (D.verschiebung m) = D'.verschiebung (f m))
    (hP : ∀ m, f (D.varpi m) = D'.varpi (f m))
    (hf : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i)
    (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (L' : D'.M →+ D'.NMod) (hL' : ∀ x : D'.M, L' (D'.verschiebung x) = D'.nMk (D'.varpi x, 0))
    (hLL' : ∀ m, L' (f m) = D.nMap D' f hV hP (L m)) (i : Fin 2) (z : D.NMod) (hz : z ∈ D.etaPiece L hL i) :
    D.nMap D' f hV hP z ∈ D'.etaPiece L' hL' i :=
  AddSubgroup.mem_inf.mpr ⟨nMap_mem_eta D D' f hV hP L hL L' hL' hLL' z (AddSubgroup.mem_inf.mp hz).1,
    nMap_mem_nPiece D D' f hV hP hf i z (AddSubgroup.mem_inf.mp hz).2⟩

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

end SdncPushKit

set_option maxHeartbeats 6400000 in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
open SdncPushKit CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule in
theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    {S : Type} [CommRing S] [IsReduced S] [IsNoetherianRing S] (g : B →+* S) (hS : (p : S) = 0)
    (hc : t.IsGradedS ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (j : Fin 2)
    (z : ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS g).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung j)
    (x : PrimeSpectrum S)
    {K : Type} [Field K] [IsAlgClosed K] (k : S →+* K) (hk : RingHom.ker k = x.asIdeal)
    (hc' : t.IsGradedS ι ψ (k.comp g))
    (L' : ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').M →+ ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').NMod) (hL' : ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').IsCanonicalLMap L')
    (hXh : (t.XS g).F.map k = (t.XS (k.comp g)).F)
    (hbcV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXh m))
    (hbcPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXh m))
    (hdiv : ∃ y ∈ ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').etaPiece L' hL'.isCartierLMap.map_verschiebung j,
      ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS (k.comp g)).toGradedCartierModuleData _ hc') (MvFormalGroup.CartierModule.baseChangeEq _ hXh) hbcV hbcPi z = p • y)
    (γ : Fin 2 → ((t.XS g).toGradedCartierModuleData _ hc).M) (hγ : ((t.XS g).toGradedCartierModuleData _ hc).IsHomogeneousVBasis γ)
    (a : Fin 2 → S) (xs : Fin 2 → ((t.XS g).toGradedCartierModuleData _ hc).M)
    (hstr : ∀ i : Fin 2, ((t.XS g).toGradedCartierModuleData _ hc).varpi (γ i) = WittVector.teichmuller p (a i) • γ (i + 1) + ((t.XS g).toGradedCartierModuleData _ hc).verschiebung (xs i))
    {S' : Type} [CommRing S'] [IsReduced S'] [IsNoetherianRing S'] (h : S →+* S')
    (x' : PrimeSpectrum S') (k' : S' →+* K) (hk' : k'.comp h = k) (hker' : RingHom.ker k' = x'.asIdeal)
    (hJ : h (a (j + 1)) = 0) (hnzd : ∀ s : S', h (a j) * s = 0 → s = 0) :
    ∃ (hch : t.IsGradedS ι ψ (h.comp g))
      (hXh' : (t.XS g).F.map h = (t.XS (h.comp g)).F)
      (hhV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh' (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
        ((t.XS (h.comp g)).toGradedCartierModuleData _ hch).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXh' m))
      (hhPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh' (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
        ((t.XS (h.comp g)).toGradedCartierModuleData _ hch).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXh' m))
      (f₀ : S') (_ : f₀ ∉ x'.asIdeal) (hc₀ : t.IsGradedS ι ψ ((algebraMap S' (Localization.Away f₀)).comp (h.comp g)))
      (L₀ : ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀).M →+ ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
      (hXr : (t.XS (h.comp g)).F.map (algebraMap S' (Localization.Away f₀)) = (t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).F)
      (hrV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS (h.comp g)).toGradedCartierModuleData _ hch).verschiebung m) =
        ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (hrPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS (h.comp g)).toGradedCartierModuleData _ hch).varpi m) =
        ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (z₀ : ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀).NMod),
      z₀ ∈ ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung j ∧
        p • z₀ = ((t.XS (h.comp g)).toGradedCartierModuleData _ hch).nMap ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXr) hrV hrPi
          (((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS (h.comp g)).toGradedCartierModuleData _ hch) (MvFormalGroup.CartierModule.baseChangeEq _ hXh') hhV hhPi z) := by
  classical
  have h11 : j + 1 + 1 = j := by fin_cases j <;> rfl

  have hpS : IsNilpotent ((p : ℕ) : S) := ⟨1, by rw [pow_one, hS]⟩
  have hS' : ((p : ℕ) : S') = 0 := by rw [← map_natCast h p, hS, map_zero]
  have hpS' : IsNilpotent ((p : ℕ) : S') := ⟨1, by rw [pow_one, hS']⟩
  have hK0 : ((p : ℕ) : K) = 0 := by rw [← map_natCast k p, hS, map_zero]
  have hpK : IsNilpotent ((p : ℕ) : K) := ⟨1, by rw [pow_one, hK0]⟩

  letI : Algebra ℤ_[p] S := (g.comp (algebraMap ℤ_[p] B)).toAlgebra
  have hγS : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) γ :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData p _ (t.XS g) hc γ hγ
  have hDS := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ (t.XS g) γ hγS hc).2

  have hch : t.IsGradedS ι ψ (h.comp g) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpS' _
  have hXm_h : (t.XS g).map h = t.XS (h.comp g) := by rw [Rigidified.XS, Rigidified.XS, FormalODModule.map_map]
  have hXh' : (t.XS g).F.map h = (t.XS (h.comp g)).F := congrArg FormalODModule.F hXm_h
  have hj_h : h.comp (Rigidified.jS ι ψ g) = (Rigidified.jS ι ψ (h.comp g)) := rfl
  set bch : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS (h.comp g)).toGradedCartierModuleData _ hch).M := CartierModule.baseChangeEq (p := p) h hXh' with hbch
  have hbca_h : IsBaseChangeAlong' h ((t.XS g).toGradedCartierModuleData _ hc) ((t.XS (h.comp g)).toGradedCartierModuleData _ hch) bch := by
    rw [hbch]; exact isBaseChangeAlong'_of_eq _ _ _ _ hγS hc _ hXm_h _ hj_h hch hXh'
  have hγh_law : (t.XS (h.comp g)).IsHomogeneousVBasis (Rigidified.jS ι ψ (h.comp g)) (fun i => bch (γ i)) :=
    ⟨fun i => hbca_h.2.2.2.2.1 i _ (hγ.1 i), by rw [hbch]; exact isUnit_det_tangent_baseChangeEq _ hXh' γ hγS.2⟩
  obtain ⟨hγh, hDh⟩ := CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ (t.XS (h.comp g)) _ hγh_law hch
  obtain ⟨Lh, hLh⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p (Rigidified.jS ι ψ (h.comp g))
    (isHausdorff_of_isNilpotent hpS') (t.XS (h.comp g)) _ hγh_law hch
  have hLL_h := CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_comp_eq p
    (Rigidified.jS ι ψ g) (Rigidified.jS ι ψ (h.comp g)) h hj_h hpS hpS' ((t.XS g).toGradedCartierModuleData _ hc) hDS ((t.XS (h.comp g)).toGradedCartierModuleData _ hch) hDh _ hbca_h L hL Lh hLh
  have hzh := nMap_mem_etaPiece ((t.XS g).toGradedCartierModuleData _ hc) ((t.XS (h.comp g)).toGradedCartierModuleData _ hch) _ hbca_h.2.2.1 hbca_h.2.2.2.1 hbca_h.2.2.2.2.1
    L hL.isCartierLMap.map_verschiebung Lh hLh.isCartierLMap.map_verschiebung hLL_h j z hz

  have hsmul_h : ∀ (s : S) (m : ((t.XS g).toGradedCartierModuleData _ hc).M), bch (WittVector.teichmuller p s • m) =
      WittVector.teichmuller p (h s) • bch m := by
    intro s m; rw [hbca_h.1, WittVector.map_teichmuller]
  have hstr_h : ∀ i : Fin 2, ((t.XS (h.comp g)).toGradedCartierModuleData _ hch).varpi (bch (γ i)) =
      WittVector.teichmuller p (h (a i)) • bch (γ (i + 1)) +
        ((t.XS (h.comp g)).toGradedCartierModuleData _ hch).verschiebung (bch (xs i)) := by
    intro i; rw [← hbca_h.2.2.2.1, hstr i, map_add, hsmul_h, hbca_h.2.2.1]
  have hnc_h : ((t.XS (h.comp g)).toGradedCartierModuleData _ hch).varpi (bch (γ j)) =
      WittVector.teichmuller p (h (a j)) • bch (γ (j + 1)) +
        ((t.XS (h.comp g)).toGradedCartierModuleData _ hch).verschiebung (bch (xs j)) := hstr_h j
  have hcrit_h : ((t.XS (h.comp g)).toGradedCartierModuleData _ hch).varpi (bch (γ (j + 1))) =
      ((t.XS (h.comp g)).toGradedCartierModuleData _ hch).verschiebung (bch (xs (j + 1))) := by
    rw [hstr_h (j + 1), hJ, WittVector.teichmuller_zero, zero_smul, zero_add]

  have hcK : t.IsGradedS ι ψ (k'.comp (h.comp g)) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpK _
  have hXm_k : (t.XS (h.comp g)).map k' = t.XS (k'.comp (h.comp g)) := by rw [Rigidified.XS, Rigidified.XS, FormalODModule.map_map]
  have hXk : (t.XS (h.comp g)).F.map k' = (t.XS (k'.comp (h.comp g))).F := congrArg FormalODModule.F hXm_k
  have hj_k : k'.comp (Rigidified.jS ι ψ (h.comp g)) = (Rigidified.jS ι ψ (k'.comp (h.comp g))) := rfl
  have hbca_k : IsBaseChangeAlong' k' ((t.XS (h.comp g)).toGradedCartierModuleData _ hch) ((t.XS (k'.comp (h.comp g))).toGradedCartierModuleData _ hcK) (CartierModule.baseChangeEq k' hXk) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγh_law hch _ hXm_k _ hj_k hcK hXk
  have hγK_law := isHomogeneousVBasis_push k' (t.XS (h.comp g)) (t.XS (k'.comp (h.comp g))) hch hcK hXk _ hγh_law hbca_k
  have hDK := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ (t.XS (k'.comp (h.comp g))) _ hγK_law hcK).2
  obtain ⟨LK, hLK⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p (Rigidified.jS ι ψ (k'.comp (h.comp g)))
    (isHausdorff_of_isNilpotent hpK) (t.XS (k'.comp (h.comp g))) _ hγK_law hcK

  letI : Algebra ℤ_[p] K := ((k.comp g).comp (algebraMap ℤ_[p] B)).toAlgebra
  obtain ⟨Sl', _, jl', φl', _, _, Dl', _, fl', hfl', Ll', _, _⟩ := hL'.exists_lift
  obtain ⟨γl', _, hγf'⟩ := hfl'.2.2.2.2.2
  have hγ'_law : (t.XS (k.comp g)).IsHomogeneousVBasis (Rigidified.jS ι ψ (k.comp g)) (fun r => fl' (γl' r)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData p _ _ hc' _ hγf'
  have hD' := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ'_law hc').2
  have hkg : k.comp g = (k'.comp (h.comp g)) := by rw [← hk', RingHom.comp_assoc]
  have hXm_e : (t.XS (k.comp g)).map (RingHom.id K) = t.XS (k'.comp (h.comp g)) := by
    rw [FormalODModule.map_id, Rigidified.XS, Rigidified.XS, hkg]
  have hXe : (t.XS (k.comp g)).F.map (RingHom.id K) = (t.XS (k'.comp (h.comp g))).F := congrArg FormalODModule.F hXm_e
  have hj_e : (RingHom.id K).comp (Rigidified.jS ι ψ (k.comp g)) = (Rigidified.jS ι ψ (k'.comp (h.comp g))) := by
    rw [RingHom.id_comp]
    show (k.comp g).comp (ψ.comp ι) = (k'.comp (h.comp g)).comp (ψ.comp ι)
    rw [hkg]
  have hbca_e : IsBaseChangeAlong' (RingHom.id K) ((t.XS (k.comp g)).toGradedCartierModuleData _ hc') ((t.XS (k'.comp (h.comp g))).toGradedCartierModuleData _ hcK) (CartierModule.baseChangeEq (RingHom.id K) hXe) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ'_law hc' _ hXm_e _ hj_e hcK hXe
  have hLL_e := CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_comp_eq p
    (Rigidified.jS ι ψ (k.comp g)) (Rigidified.jS ι ψ (k'.comp (h.comp g))) (RingHom.id K) hj_e hpK hpK ((t.XS (k.comp g)).toGradedCartierModuleData _ hc') hD' ((t.XS (k'.comp (h.comp g))).toGradedCartierModuleData _ hcK) hDK _ hbca_e L' hL' LK hLK
  obtain ⟨y, hy, hNz⟩ := hdiv
  have hy'' := nMap_mem_etaPiece ((t.XS (k.comp g)).toGradedCartierModuleData _ hc') ((t.XS (k'.comp (h.comp g))).toGradedCartierModuleData _ hcK) _ hbca_e.2.2.1 hbca_e.2.2.2.1 hbca_e.2.2.2.2.1
    L' hL'.isCartierLMap.map_verschiebung LK hLK.isCartierLMap.map_verschiebung hLL_e j y hy

  have hsq : ∀ m : CartierModule p (t.XS g).F,
      CartierModule.baseChangeEq (RingHom.id K) hXe (CartierModule.baseChangeEq k hXh m) =
      CartierModule.baseChangeEq k' hXk (bch m) := by
    intro m
    rw [hbch]
    apply MvFormalGroup.CartierModule.ext
    funext n
    show MvPowerSeries.map (RingHom.id K) (MvPowerSeries.map k (m.toPowerSeries n)) =
      MvPowerSeries.map k' (MvPowerSeries.map h (m.toPowerSeries n))
    rw [MvPowerSeries.map_map, MvPowerSeries.map_map, RingHom.id_comp, hk']
  have hkV : ∀ m, ((CartierModule.baseChangeEq k' hXk).comp bch) (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS (k'.comp (h.comp g))).toGradedCartierModuleData _ hcK).verschiebung (((CartierModule.baseChangeEq k' hXk).comp bch) m) := fun m =>
    (congrArg (CartierModule.baseChangeEq k' hXk) (hbca_h.2.2.1 m)).trans (hbca_k.2.2.1 _)
  have hkP : ∀ m, ((CartierModule.baseChangeEq k' hXk).comp bch) (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS (k'.comp (h.comp g))).toGradedCartierModuleData _ hcK).varpi (((CartierModule.baseChangeEq k' hXk).comp bch) m) := fun m =>
    (congrArg (CartierModule.baseChangeEq k' hXk) (hbca_h.2.2.2.1 m)).trans (hbca_k.2.2.2.1 _)
  have e1 := nMap_nMap_eq ((t.XS g).toGradedCartierModuleData _ hc) ((t.XS (k.comp g)).toGradedCartierModuleData _ hc') ((t.XS (k'.comp (h.comp g))).toGradedCartierModuleData _ hcK)
      (CartierModule.baseChangeEq _ hXh) hbcV hbcPi
      (CartierModule.baseChangeEq (RingHom.id K) hXe) hbca_e.2.2.1 hbca_e.2.2.2.1
      ((CartierModule.baseChangeEq k' hXk).comp bch) hkV hkP hsq z
  have e2 := nMap_nMap_eq ((t.XS g).toGradedCartierModuleData _ hc) ((t.XS (h.comp g)).toGradedCartierModuleData _ hch) ((t.XS (k'.comp (h.comp g))).toGradedCartierModuleData _ hcK)
      bch hbca_h.2.2.1 hbca_h.2.2.2.1
      (CartierModule.baseChangeEq k' hXk) hbca_k.2.2.1 hbca_k.2.2.2.1
      ((CartierModule.baseChangeEq k' hXk).comp bch) hkV hkP (fun _ => rfl) z
  have hdiv'' : ∃ y'' ∈ ((t.XS (k'.comp (h.comp g))).toGradedCartierModuleData _ hcK).etaPiece LK hLK.isCartierLMap.map_verschiebung j,
      ((t.XS (h.comp g)).toGradedCartierModuleData _ hch).nMap ((t.XS (k'.comp (h.comp g))).toGradedCartierModuleData _ hcK) (CartierModule.baseChangeEq _ hXk) hbca_k.2.2.1 hbca_k.2.2.2.1
        (((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS (h.comp g)).toGradedCartierModuleData _ hch) bch hbca_h.2.2.1 hbca_h.2.2.2.1 z) = p • y'' := by
    refine ⟨_, hy'', ?_⟩
    rw [e2, ← e1, hNz, map_nsmul]

  obtain ⟨f₀, hf₀, hc₀, L₀, hL₀, hXr, hrV, hrPi, z₀, hz₀, heq⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_teichmuller_smul_add_verschiebung
      p ι Φ ψ hB t ht (h.comp g) hS' hch Lh hLh j (fun i => bch (γ i)) hγh
      (h (a j)) hnzd (bch (xs j)) hnc_h (bch (xs (j + 1))) hcrit_h
      _ hzh x' k' hker' hcK LK hLK hXk hbca_k.2.2.1 hbca_k.2.2.2.1 hdiv''
  exact ⟨hch, hXh', hbca_h.2.2.1, hbca_h.2.2.2.1, f₀, hf₀, hc₀, L₀, hL₀, hXr, hrV, hrPi, z₀, hz₀, heq⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_nMap_of_map_eq_zero_of_forall_mul_eq_zero_of_nMap_eq_smul
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_nMap_of_map_eq_zero_of_forall_mul_eq_zero_of_nMap_eq_smul (solution)
