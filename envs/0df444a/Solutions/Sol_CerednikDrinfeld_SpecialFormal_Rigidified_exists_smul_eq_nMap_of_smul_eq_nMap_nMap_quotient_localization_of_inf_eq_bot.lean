-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_smul_eq_nMap_nMap_quotient_localization_of_inf_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/bd0da875-00cb-572e-8646-5a1d82c6ecd1

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
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_mem_etaPiece_smul_eq_of_smul_eq_nMap_quotient_of_inf_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_smul_eq_nMap_nMap_quotient_localization_of_inf_eq_bot
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace LocalMilnorKit

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

end LocalMilnorKit

open LocalMilnorKit CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

theorem LocalMilnorKit.transportStratum
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    {S : Type} [CommRing S] (g : B →+* S) (hc : t.IsGradedS ι ψ g)
    (γ : Fin 2 → MvFormalGroup.CartierModule p (t.XS g).F) (hγ : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) γ)
    (z : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod) (j : Fin 2)
    {S₁ : Type} [CommRing S₁] (μ : S →+* S₁) (hc₁ : t.IsGradedS ι ψ (μ.comp g))
    (hX₁ : (t.XS g).F.map μ = (t.XS (μ.comp g)).F)
    (hV₁ : ∀ m, (MvFormalGroup.CartierModule.baseChangeEq _ hX₁) (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).verschiebung m) = ((t.XS (μ.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (μ.comp g)) hc₁).verschiebung ((MvFormalGroup.CartierModule.baseChangeEq _ hX₁) m))
    (hP₁ : ∀ m, (MvFormalGroup.CartierModule.baseChangeEq _ hX₁) (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).varpi m) = ((t.XS (μ.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (μ.comp g)) hc₁).varpi ((MvFormalGroup.CartierModule.baseChangeEq _ hX₁) m))
    {T : Type} [CommRing T] (α : S₁ →+* T) (hpT : IsNilpotent ((p : ℕ) : T)) (hcT : t.IsGradedS ι ψ (α.comp (μ.comp g)))
    (LT : ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT).M →+ ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT).NMod) (hLT : ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT).IsCanonicalLMap LT)
    (hXT : (t.XS (μ.comp g)).F.map α = (t.XS (α.comp (μ.comp g))).F)
    (hVT : ∀ m, (MvFormalGroup.CartierModule.baseChangeEq _ hXT) (((t.XS (μ.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (μ.comp g)) hc₁).verschiebung m) = ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT).verschiebung ((MvFormalGroup.CartierModule.baseChangeEq _ hXT) m))
    (hPT : ∀ m, (MvFormalGroup.CartierModule.baseChangeEq _ hXT) (((t.XS (μ.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (μ.comp g)) hc₁).varpi m) = ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT).varpi ((MvFormalGroup.CartierModule.baseChangeEq _ hXT) m))
    (z' : ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT).NMod) (hz' : z' ∈ ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT).etaPiece LT hLT.isCartierLMap.map_verschiebung j)
    (heq : p • z' = ((t.XS (μ.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (μ.comp g)) hc₁).nMap ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT) (MvFormalGroup.CartierModule.baseChangeEq _ hXT) hVT hPT (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS (μ.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (μ.comp g)) hc₁) (MvFormalGroup.CartierModule.baseChangeEq _ hX₁) hV₁ hP₁ z))
    {R : Type} [CommRing R] (res : S →+* R) (hcR : t.IsGradedS ι ψ (res.comp g))
    (hXres : (t.XS g).F.map res = (t.XS (res.comp g)).F)
    (hVres : ∀ m, (MvFormalGroup.CartierModule.baseChangeEq _ hXres) (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).verschiebung m) = ((t.XS (res.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (res.comp g)) hcR).verschiebung ((MvFormalGroup.CartierModule.baseChangeEq _ hXres) m))
    (hPres : ∀ m, (MvFormalGroup.CartierModule.baseChangeEq _ hXres) (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).varpi m) = ((t.XS (res.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (res.comp g)) hcR).varpi ((MvFormalGroup.CartierModule.baseChangeEq _ hXres) m))
    {R' : Type} [CommRing R'] (ν : R →+* R') (hpR' : IsNilpotent ((p : ℕ) : R'))
    (φ : T →+* R') (hφ : φ.comp (α.comp μ) = ν.comp res) :
    ∃ (hcI : t.IsGradedS ι ψ (ν.comp (res.comp g)))
      (LI : ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI).M →+ ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI).NMod) (hLI : ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI).IsCanonicalLMap LI)
      (hXI : (t.XS (res.comp g)).F.map ν = (t.XS (ν.comp (res.comp g))).F)
      (hVI : ∀ m, (MvFormalGroup.CartierModule.baseChangeEq _ hXI) (((t.XS (res.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (res.comp g)) hcR).verschiebung m) = ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI).verschiebung ((MvFormalGroup.CartierModule.baseChangeEq _ hXI) m))
      (hPI : ∀ m, (MvFormalGroup.CartierModule.baseChangeEq _ hXI) (((t.XS (res.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (res.comp g)) hcR).varpi m) = ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI).varpi ((MvFormalGroup.CartierModule.baseChangeEq _ hXI) m))
      (zI : ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI).NMod),
      zI ∈ ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI).etaPiece LI hLI.isCartierLMap.map_verschiebung j ∧
        p • zI = ((t.XS (res.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (res.comp g)) hcR).nMap ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI) (MvFormalGroup.CartierModule.baseChangeEq _ hXI) hVI hPI (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS (res.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (res.comp g)) hcR) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) hVres hPres z) := by
  classical
  have hcI : t.IsGradedS ι ψ (ν.comp (res.comp g)) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpR' _
  have hXm₁ : (t.XS g).map μ = t.XS (μ.comp g) := by rw [FormalODModule.map_map]
  have hj₁ : μ.comp (Rigidified.jS ι ψ g) = Rigidified.jS ι ψ (μ.comp g) := rfl
  have hbca₁ : IsBaseChangeAlong' μ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t.XS (μ.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (μ.comp g)) hc₁) (MvFormalGroup.CartierModule.baseChangeEq _ hX₁) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXm₁ _ hj₁ hc₁ hX₁
  have hγ₁ := isHomogeneousVBasis_push μ (t.XS g) (t.XS (μ.comp g)) hc hc₁ hX₁ _ hγ hbca₁
  have hXmT : (t.XS (μ.comp g)).map α = t.XS (α.comp (μ.comp g)) := by rw [FormalODModule.map_map]
  have hjT : α.comp (Rigidified.jS ι ψ (μ.comp g)) = Rigidified.jS ι ψ (α.comp (μ.comp g)) := rfl
  have hbcaT : IsBaseChangeAlong' α ((t.XS (μ.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (μ.comp g)) hc₁) ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT) (MvFormalGroup.CartierModule.baseChangeEq _ hXT) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ₁ hc₁ _ hXmT _ hjT hcT hXT
  have hγT := isHomogeneousVBasis_push α (t.XS (μ.comp g)) (t.XS (α.comp (μ.comp g))) hc₁ hcT hXT _ hγ₁ hbcaT
  have hXmR : (t.XS g).map res = t.XS (res.comp g) := by rw [FormalODModule.map_map]
  have hjR : res.comp (Rigidified.jS ι ψ g) = Rigidified.jS ι ψ (res.comp g) := rfl
  have hbcaR : IsBaseChangeAlong' res ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t.XS (res.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (res.comp g)) hcR) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXmR _ hjR hcR hXres
  have hγR := isHomogeneousVBasis_push res (t.XS g) (t.XS (res.comp g)) hc hcR hXres _ hγ hbcaR
  have hXmI : (t.XS (res.comp g)).map ν = t.XS (ν.comp (res.comp g)) := by rw [FormalODModule.map_map]
  have hXI : (t.XS (res.comp g)).F.map ν = (t.XS (ν.comp (res.comp g))).F := congrArg FormalODModule.F hXmI
  have hjI : ν.comp (Rigidified.jS ι ψ (res.comp g)) = Rigidified.jS ι ψ (ν.comp (res.comp g)) := rfl
  have hbcaI : IsBaseChangeAlong' ν ((t.XS (res.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (res.comp g)) hcR) ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI) (MvFormalGroup.CartierModule.baseChangeEq _ hXI) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγR hcR _ hXmI _ hjI hcI hXI
  have hγI := isHomogeneousVBasis_push ν (t.XS (res.comp g)) (t.XS (ν.comp (res.comp g))) hcR hcI hXI _ hγR hbcaI
  have hφg : φ.comp (α.comp (μ.comp g)) = ν.comp (res.comp g) :=
    RingHom.ext fun b => by simpa only [RingHom.comp_apply] using RingHom.congr_fun hφ (g b)
  have hXmφ : (t.XS (α.comp (μ.comp g))).map φ = t.XS (ν.comp (res.comp g)) := by rw [FormalODModule.map_map, hφg]
  have hXφ : (t.XS (α.comp (μ.comp g))).F.map φ = (t.XS (ν.comp (res.comp g))).F := congrArg FormalODModule.F hXmφ
  have hjφ : φ.comp (Rigidified.jS ι ψ (α.comp (μ.comp g))) = Rigidified.jS ι ψ (ν.comp (res.comp g)) := by
    show φ.comp ((α.comp (μ.comp g)).comp (structureMap ι ψ)) = (ν.comp (res.comp g)).comp (structureMap ι ψ)
    rw [← RingHom.comp_assoc, hφg]
  have hbcaφ : IsBaseChangeAlong' φ ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT) ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI) (MvFormalGroup.CartierModule.baseChangeEq φ hXφ) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγT hcT _ hXmφ _ hjφ hcI hXφ
  have hDT := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγT hcT).2
  have hDI := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγI hcI).2
  obtain ⟨LI, hLI⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (Rigidified.jS ι ψ (ν.comp (res.comp g))) (isHausdorff_of_isNilpotent hpR') _ _ hγI hcI
  have hLLφ := natL_of_eq _ _ hpT hpR' _ hDT _ hjφ _ hDI _ hbcaφ LT hLT LI hLI
  have hz'E := (AddSubgroup.mem_inf.mp hz').1
  have hz'P := (AddSubgroup.mem_inf.mp hz').2
  have hzI_eta := nMap_mem_eta _ _ _ hbcaφ.2.2.1 hbcaφ.2.2.2.1 LT hLT.isCartierLMap.map_verschiebung LI hLI.isCartierLMap.map_verschiebung hLLφ z' hz'E
  have hzI_piece := nMap_mem_nPiece _ _ _ hbcaφ.2.2.1 hbcaφ.2.2.2.1 hbcaφ.2.2.2.2.1 j z' hz'P
  have hsq : ∀ m : MvFormalGroup.CartierModule p (t.XS g).F,
      (MvFormalGroup.CartierModule.baseChangeEq φ hXφ) ((MvFormalGroup.CartierModule.baseChangeEq _ hXT) ((MvFormalGroup.CartierModule.baseChangeEq _ hX₁) m)) = (MvFormalGroup.CartierModule.baseChangeEq _ hXI) ((MvFormalGroup.CartierModule.baseChangeEq _ hXres) m) := by
    intro m
    apply MvFormalGroup.CartierModule.ext
    funext k
    show MvPowerSeries.map φ (MvPowerSeries.map α (MvPowerSeries.map μ (m.toPowerSeries k))) =
      MvPowerSeries.map ν (MvPowerSeries.map res (m.toPowerSeries k))
    rw [MvPowerSeries.map_map, MvPowerSeries.map_map, MvPowerSeries.map_map, RingHom.comp_assoc, hφ]
  have hkV : ∀ m, ((MvFormalGroup.CartierModule.baseChangeEq _ hXI).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).verschiebung m) = ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI).verschiebung (((MvFormalGroup.CartierModule.baseChangeEq _ hXI).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) m) := fun m =>
    (congrArg (MvFormalGroup.CartierModule.baseChangeEq _ hXI) (hVres m)).trans (hbcaI.2.2.1 _)
  have hkP : ∀ m, ((MvFormalGroup.CartierModule.baseChangeEq _ hXI).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).varpi m) = ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI).varpi (((MvFormalGroup.CartierModule.baseChangeEq _ hXI).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) m) := fun m =>
    (congrArg (MvFormalGroup.CartierModule.baseChangeEq _ hXI) (hPres m)).trans (hbcaI.2.2.2.1 _)
  have hk2V : ∀ m, ((MvFormalGroup.CartierModule.baseChangeEq _ hXT).comp (MvFormalGroup.CartierModule.baseChangeEq _ hX₁)) (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).verschiebung m) = ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT).verschiebung (((MvFormalGroup.CartierModule.baseChangeEq _ hXT).comp (MvFormalGroup.CartierModule.baseChangeEq _ hX₁)) m) := fun m =>
    (congrArg (MvFormalGroup.CartierModule.baseChangeEq _ hXT) (hV₁ m)).trans (hVT _)
  have hk2P : ∀ m, ((MvFormalGroup.CartierModule.baseChangeEq _ hXT).comp (MvFormalGroup.CartierModule.baseChangeEq _ hX₁)) (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).varpi m) = ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT).varpi (((MvFormalGroup.CartierModule.baseChangeEq _ hXT).comp (MvFormalGroup.CartierModule.baseChangeEq _ hX₁)) m) := fun m =>
    (congrArg (MvFormalGroup.CartierModule.baseChangeEq _ hXT) (hP₁ m)).trans (hPT _)
  have e1 : ((t.XS (res.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (res.comp g)) hcR).nMap ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI) (MvFormalGroup.CartierModule.baseChangeEq _ hXI) hbcaI.2.2.1 hbcaI.2.2.2.1 (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS (res.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (res.comp g)) hcR) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) hVres hPres z) = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI) ((MvFormalGroup.CartierModule.baseChangeEq _ hXI).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) hkV hkP z :=
    nMap_nMap_eq ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t.XS (res.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (res.comp g)) hcR) ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) hVres hPres (MvFormalGroup.CartierModule.baseChangeEq _ hXI) hbcaI.2.2.1 hbcaI.2.2.2.1 ((MvFormalGroup.CartierModule.baseChangeEq _ hXI).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) hkV hkP (fun _ => rfl) z
  have e2a : ((t.XS (μ.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (μ.comp g)) hc₁).nMap ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT) (MvFormalGroup.CartierModule.baseChangeEq _ hXT) hVT hPT (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS (μ.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (μ.comp g)) hc₁) (MvFormalGroup.CartierModule.baseChangeEq _ hX₁) hV₁ hP₁ z) = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT) ((MvFormalGroup.CartierModule.baseChangeEq _ hXT).comp (MvFormalGroup.CartierModule.baseChangeEq _ hX₁)) hk2V hk2P z :=
    nMap_nMap_eq ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t.XS (μ.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (μ.comp g)) hc₁) ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT) (MvFormalGroup.CartierModule.baseChangeEq _ hX₁) hV₁ hP₁ (MvFormalGroup.CartierModule.baseChangeEq _ hXT) hVT hPT ((MvFormalGroup.CartierModule.baseChangeEq _ hXT).comp (MvFormalGroup.CartierModule.baseChangeEq _ hX₁)) hk2V hk2P (fun _ => rfl) z
  have e2b : ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT).nMap ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI) (MvFormalGroup.CartierModule.baseChangeEq φ hXφ) hbcaφ.2.2.1 hbcaφ.2.2.2.1 (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT) ((MvFormalGroup.CartierModule.baseChangeEq _ hXT).comp (MvFormalGroup.CartierModule.baseChangeEq _ hX₁)) hk2V hk2P z) = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI) ((MvFormalGroup.CartierModule.baseChangeEq _ hXI).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) hkV hkP z :=
    nMap_nMap_eq ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT) ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI) ((MvFormalGroup.CartierModule.baseChangeEq _ hXT).comp (MvFormalGroup.CartierModule.baseChangeEq _ hX₁)) hk2V hk2P (MvFormalGroup.CartierModule.baseChangeEq φ hXφ) hbcaφ.2.2.1 hbcaφ.2.2.2.1 ((MvFormalGroup.CartierModule.baseChangeEq _ hXI).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) hkV hkP (fun m => hsq m) z
  have hdivI : p • (((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT).nMap ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI) (MvFormalGroup.CartierModule.baseChangeEq φ hXφ) hbcaφ.2.2.1 hbcaφ.2.2.2.1 z') = ((t.XS (res.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (res.comp g)) hcR).nMap ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI) (MvFormalGroup.CartierModule.baseChangeEq _ hXI) hbcaI.2.2.1 hbcaI.2.2.2.1 (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS (res.comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ (res.comp g)) hcR) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) hVres hPres z) :=
    (map_nsmul (((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT).nMap ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI) (MvFormalGroup.CartierModule.baseChangeEq φ hXφ) hbcaφ.2.2.1 hbcaφ.2.2.2.1) p z').symm.trans
      ((congrArg (((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT).nMap ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI) (MvFormalGroup.CartierModule.baseChangeEq φ hXφ) hbcaφ.2.2.1 hbcaφ.2.2.2.1) heq).trans
        ((congrArg (((t.XS (α.comp (μ.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (α.comp (μ.comp g))) hcT).nMap ((t.XS (ν.comp (res.comp g))).toGradedCartierModuleData (Rigidified.jS ι ψ (ν.comp (res.comp g))) hcI) (MvFormalGroup.CartierModule.baseChangeEq φ hXφ) hbcaφ.2.2.1 hbcaφ.2.2.2.1) e2a).trans (e2b.trans e1.symm)))
  exact ⟨hcI, LI, hLI, hXI, hbcaI.2.2.1, hbcaI.2.2.2.1, _, AddSubgroup.mem_inf.mpr ⟨hzI_eta, hzI_piece⟩, hdivI⟩

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (t : Rigidified p Φ B)
    {S : Type} [CommRing S] [IsNoetherianRing S] (g : B →+* S) (hS : (p : S) = 0)
    (hc : t.IsGradedS ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (j : Fin 2)
    (z : ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS g).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung j)
    (x : PrimeSpectrum S)
    (J₀ J₁ : Ideal S) (hJ : J₀ ⊓ J₁ = ⊥)

    (hcq₀ : t.IsGradedS ι ψ ((Ideal.Quotient.mk J₀).comp g))
    (hXq₀ : (t.XS g).F.map (Ideal.Quotient.mk J₀) = (t.XS ((Ideal.Quotient.mk J₀).comp g)).F)
    (hVq₀ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXq₀ (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXq₀ m))
    (hPq₀ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXq₀ (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXq₀ m))
    (x₀' : PrimeSpectrum (S ⧸ J₀)) (hx₀' : x₀'.asIdeal.comap (Ideal.Quotient.mk J₀) = x.asIdeal)
    (f₀' : S ⧸ J₀) (hf₀' : f₀' ∉ x₀'.asIdeal)
    (hc₀' : t.IsGradedS ι ψ ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g)))
    (L₀' : ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').M →+ ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').NMod) (hL₀' : ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').IsCanonicalLMap L₀')
    (hX₀' : (t.XS ((Ideal.Quotient.mk J₀).comp g)).F.map (algebraMap (S ⧸ J₀) (Localization.Away f₀')) = (t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).F)
    (hV₀' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₀' (((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀).verschiebung m) =
      ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hX₀' m))
    (hP₀' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₀' (((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀).varpi m) =
      ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hX₀' m))
    (z₀' : ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').NMod) (hz₀' : z₀' ∈ ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').etaPiece L₀' hL₀'.isCartierLMap.map_verschiebung j)
    (heq₀ : p • z₀' = ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀).nMap ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀') (MvFormalGroup.CartierModule.baseChangeEq _ hX₀') hV₀' hP₀'
      (((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXq₀) hVq₀ hPq₀ z))

    (hcq₁ : t.IsGradedS ι ψ ((Ideal.Quotient.mk J₁).comp g))
    (hXq₁ : (t.XS g).F.map (Ideal.Quotient.mk J₁) = (t.XS ((Ideal.Quotient.mk J₁).comp g)).F)
    (hVq₁ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXq₁ (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXq₁ m))
    (hPq₁ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXq₁ (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXq₁ m))
    (x₁' : PrimeSpectrum (S ⧸ J₁)) (hx₁' : x₁'.asIdeal.comap (Ideal.Quotient.mk J₁) = x.asIdeal)
    (f₁' : S ⧸ J₁) (hf₁' : f₁' ∉ x₁'.asIdeal)
    (hc₁' : t.IsGradedS ι ψ ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g)))
    (L₁' : ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').M →+ ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').NMod) (hL₁' : ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').IsCanonicalLMap L₁')
    (hX₁' : (t.XS ((Ideal.Quotient.mk J₁).comp g)).F.map (algebraMap (S ⧸ J₁) (Localization.Away f₁')) = (t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).F)
    (hV₁' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₁' (((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁).verschiebung m) =
      ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hX₁' m))
    (hP₁' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₁' (((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁).varpi m) =
      ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hX₁' m))
    (z₁' : ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').NMod) (hz₁' : z₁' ∈ ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').etaPiece L₁' hL₁'.isCartierLMap.map_verschiebung j)
    (heq₁ : p • z₁' = ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁).nMap ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁') (MvFormalGroup.CartierModule.baseChangeEq _ hX₁') hV₁' hP₁'
      (((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁) (MvFormalGroup.CartierModule.baseChangeEq _ hXq₁) hVq₁ hPq₁ z)) :
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

  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective f₀'
  obtain ⟨a₁, ha₁⟩ := Ideal.Quotient.mk_surjective f₁'
  have ha₀x : a₀ ∉ x.asIdeal := by
    intro h; rw [← hx₀'] at h; apply hf₀'; rw [← ha₀]; exact h
  have ha₁x : a₁ ∉ x.asIdeal := by
    intro h; rw [← hx₁'] at h; apply hf₁'; rw [← ha₁]; exact h
  have hfx : a₀ * a₁ ∉ x.asIdeal := fun h => (x.isPrime.mem_or_mem h).elim ha₀x ha₁x
  have hdvd₀ : a₀ ∣ a₀ * a₁ := dvd_mul_right a₀ a₁
  have hdvd₁ : a₁ ∣ a₀ * a₁ := dvd_mul_left a₁ a₀

  have hpR : IsNilpotent ((p : ℕ) : Localization.Away (a₀ * a₁)) := by
    simpa only [map_natCast] using hpS.map (algebraMap S (Localization.Away (a₀ * a₁)))
  have hp0R : ((p : ℕ) : Localization.Away (a₀ * a₁)) = 0 := by
    rw [← map_natCast (algebraMap S (Localization.Away (a₀ * a₁))) p, hS, map_zero]

  obtain ⟨I₀, hI₀⟩ : ∃ I : Ideal (Localization.Away (a₀ * a₁)), I = J₀.map (algebraMap S (Localization.Away (a₀ * a₁))) := ⟨_, rfl⟩
  obtain ⟨I₁, hI₁⟩ : ∃ I : Ideal (Localization.Away (a₀ * a₁)), I = J₁.map (algebraMap S (Localization.Away (a₀ * a₁))) := ⟨_, rfl⟩
  have hI : I₀ ⊓ I₁ = ⊥ := by
    rw [hI₀, hI₁, eq_bot_iff]
    rintro r ⟨hr₀, hr₁⟩
    obtain ⟨⟨⟨j₀, hj₀⟩, s₀⟩, e₀⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers (a₀ * a₁)) (Localization.Away (a₀ * a₁))).mp hr₀
    obtain ⟨⟨⟨j₁, hj₁⟩, s₁⟩, e₁⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers (a₀ * a₁)) (Localization.Away (a₀ * a₁))).mp hr₁

    have h01 : algebraMap S (Localization.Away (a₀ * a₁)) (j₀ * s₁) = algebraMap S (Localization.Away (a₀ * a₁)) (j₁ * s₀) := by
      simp only [map_mul]
      rw [← e₀, ← e₁]; ring
    obtain ⟨⟨u, hu⟩, hu'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (a₀ * a₁)) (Localization.Away (a₀ * a₁))).mp h01
    have hmem : u * (j₀ * (s₁ : S)) ∈ J₀ ⊓ J₁ := by
      refine ⟨J₀.mul_mem_left _ (J₀.mul_mem_right _ hj₀), ?_⟩
      simp only at hu'
      rw [hu']
      exact J₁.mul_mem_left _ (J₁.mul_mem_right _ hj₁)
    rw [hJ, Submodule.mem_bot] at hmem
    have hus : IsUnit (algebraMap S (Localization.Away (a₀ * a₁)) (u * (s₁ : S))) :=
      IsLocalization.map_units (Localization.Away (a₀ * a₁)) (⟨u * (s₁ : S), Submonoid.mul_mem _ hu s₁.2⟩ : Submonoid.powers (a₀ * a₁))
    have hj0 : algebraMap S (Localization.Away (a₀ * a₁)) j₀ = 0 := by
      have : algebraMap S (Localization.Away (a₀ * a₁)) j₀ * algebraMap S (Localization.Away (a₀ * a₁)) (u * (s₁ : S)) = 0 := by
        rw [← map_mul, show j₀ * (u * (s₁ : S)) = u * (j₀ * (s₁ : S)) by ring, hmem, map_zero]
      exact (hus.mul_left_eq_zero).mp this
    have : r * algebraMap S (Localization.Away (a₀ * a₁)) (s₀ : S) = 0 := by rw [e₀, hj0]
    exact (Submodule.mem_bot _).mpr (((IsLocalization.map_units (Localization.Away (a₀ * a₁)) s₀).mul_left_eq_zero).mp this)

  have hcR : t.IsGradedS ι ψ ((algebraMap S (Localization.Away (a₀ * a₁))).comp g) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpR _
  have hXm_res : (t.XS g).map (algebraMap S (Localization.Away (a₀ * a₁))) = t.XS ((algebraMap S (Localization.Away (a₀ * a₁))).comp g) := by
    rw [FormalODModule.map_map]
  have hXres : (t.XS g).F.map (algebraMap S (Localization.Away (a₀ * a₁))) = (t.XS ((algebraMap S (Localization.Away (a₀ * a₁))).comp g)).F :=
    congrArg FormalODModule.F hXm_res
  have hj_res : (algebraMap S (Localization.Away (a₀ * a₁))).comp (Rigidified.jS ι ψ g) = Rigidified.jS ι ψ ((algebraMap S (Localization.Away (a₀ * a₁))).comp g) := rfl
  letI : Algebra ℤ_[p] S := (g.comp (algebraMap ℤ_[p] B)).toAlgebra
  obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL.exists_lift
  obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
  have hγ : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) (fun k => fl (γl k)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData p _ _ hc _ hγf
  have hbca_res : IsBaseChangeAlong' (algebraMap S (Localization.Away (a₀ * a₁))) ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t.XS ((algebraMap S (Localization.Away (a₀ * a₁))).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away (a₀ * a₁))).comp g)) hcR) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXm_res _ hj_res hcR hXres
  have hγR := isHomogeneousVBasis_push (algebraMap S (Localization.Away (a₀ * a₁))) (t.XS g) (t.XS ((algebraMap S (Localization.Away (a₀ * a₁))).comp g)) hc hcR hXres _ hγ hbca_res
  have hD := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ hc).2
  have hDR := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγR hcR).2
  obtain ⟨LR, hLR⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (Rigidified.jS ι ψ ((algebraMap S (Localization.Away (a₀ * a₁))).comp g)) (isHausdorff_of_isNilpotent hpR) _ _ hγR hcR
  have hLL_res := natL_of_eq _ _ hpS hpR _ hD _ hj_res _ hDR _ hbca_res L hL LR hLR
  have hzE := (AddSubgroup.mem_inf.mp hz).1
  have hzP := (AddSubgroup.mem_inf.mp hz).2
  have hNz_eta := nMap_mem_eta _ _ _ hbca_res.2.2.1 hbca_res.2.2.2.1 L hL.isCartierLMap.map_verschiebung LR hLR.isCartierLMap.map_verschiebung hLL_res z hzE
  have hNz_piece := nMap_mem_nPiece _ _ _ hbca_res.2.2.1 hbca_res.2.2.2.1 hbca_res.2.2.2.2.1 j z hzP

  have hpJ₀ : IsNilpotent ((p : ℕ) : S ⧸ J₀) := by
    simpa only [map_natCast] using hpS.map (Ideal.Quotient.mk J₀)
  have hpT₀ : IsNilpotent ((p : ℕ) : Localization.Away f₀') := by
    simpa only [map_natCast] using hpJ₀.map (algebraMap (S ⧸ J₀) (Localization.Away f₀'))
  have hpI₀ : IsNilpotent ((p : ℕ) : Localization.Away (a₀ * a₁) ⧸ I₀) := by
    simpa only [map_natCast] using hpR.map (Ideal.Quotient.mk I₀)
  have hJI₀ : J₀ ≤ I₀.comap (algebraMap S (Localization.Away (a₀ * a₁))) := by rw [hI₀]; exact Ideal.le_comap_map
  have hunit₀ : IsUnit ((Ideal.quotientMap I₀ (algebraMap S (Localization.Away (a₀ * a₁))) hJI₀) f₀') := by
    rw [← ha₀, Ideal.quotientMap_mk]
    exact (IsLocalization.Away.isUnit_of_dvd (a₀ * a₁) (S := Localization.Away (a₀ * a₁)) hdvd₀).map (Ideal.Quotient.mk I₀)
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ : Localization.Away f₀' →+* Localization.Away (a₀ * a₁) ⧸ I₀,
      φ.comp ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp (Ideal.Quotient.mk J₀)) = (Ideal.Quotient.mk I₀).comp (algebraMap S (Localization.Away (a₀ * a₁))) :=
    ⟨IsLocalization.Away.lift f₀' hunit₀, by
      rw [← RingHom.comp_assoc, IsLocalization.Away.lift_comp, Ideal.quotientMap_comp_mk]⟩
  obtain ⟨hcI₀, LI₀, hLI₀, hXI₀, hVI₀, hPI₀, zI₀, hzI₀, hdivI₀⟩ :=
    LocalMilnorKit.transportStratum p ι Φ ψ t g hc _ hγ z j
      (Ideal.Quotient.mk J₀) hcq₀ hXq₀ hVq₀ hPq₀
      (algebraMap (S ⧸ J₀) (Localization.Away f₀')) hpT₀ hc₀' L₀' hL₀' hX₀' hV₀' hP₀' z₀' hz₀' heq₀
      (algebraMap S (Localization.Away (a₀ * a₁))) hcR hXres hbca_res.2.2.1 hbca_res.2.2.2.1
      (Ideal.Quotient.mk I₀) hpI₀ φ₀ hφ₀

  have hpJ₁ : IsNilpotent ((p : ℕ) : S ⧸ J₁) := by
    simpa only [map_natCast] using hpS.map (Ideal.Quotient.mk J₁)
  have hpT₁ : IsNilpotent ((p : ℕ) : Localization.Away f₁') := by
    simpa only [map_natCast] using hpJ₁.map (algebraMap (S ⧸ J₁) (Localization.Away f₁'))
  have hpI₁ : IsNilpotent ((p : ℕ) : Localization.Away (a₀ * a₁) ⧸ I₁) := by
    simpa only [map_natCast] using hpR.map (Ideal.Quotient.mk I₁)
  have hJI₁ : J₁ ≤ I₁.comap (algebraMap S (Localization.Away (a₀ * a₁))) := by rw [hI₁]; exact Ideal.le_comap_map
  have hunit₁ : IsUnit ((Ideal.quotientMap I₁ (algebraMap S (Localization.Away (a₀ * a₁))) hJI₁) f₁') := by
    rw [← ha₁, Ideal.quotientMap_mk]
    exact (IsLocalization.Away.isUnit_of_dvd (a₀ * a₁) (S := Localization.Away (a₀ * a₁)) hdvd₁).map (Ideal.Quotient.mk I₁)
  obtain ⟨φ₁, hφ₁⟩ : ∃ φ : Localization.Away f₁' →+* Localization.Away (a₀ * a₁) ⧸ I₁,
      φ.comp ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp (Ideal.Quotient.mk J₁)) = (Ideal.Quotient.mk I₁).comp (algebraMap S (Localization.Away (a₀ * a₁))) :=
    ⟨IsLocalization.Away.lift f₁' hunit₁, by
      rw [← RingHom.comp_assoc, IsLocalization.Away.lift_comp, Ideal.quotientMap_comp_mk]⟩
  obtain ⟨hcI₁, LI₁, hLI₁, hXI₁, hVI₁, hPI₁, zI₁, hzI₁, hdivI₁⟩ :=
    LocalMilnorKit.transportStratum p ι Φ ψ t g hc _ hγ z j
      (Ideal.Quotient.mk J₁) hcq₁ hXq₁ hVq₁ hPq₁
      (algebraMap (S ⧸ J₁) (Localization.Away f₁')) hpT₁ hc₁' L₁' hL₁' hX₁' hV₁' hP₁' z₁' hz₁' heq₁
      (algebraMap S (Localization.Away (a₀ * a₁))) hcR hXres hbca_res.2.2.1 hbca_res.2.2.2.1
      (Ideal.Quotient.mk I₁) hpI₁ φ₁ hφ₁

  obtain ⟨w, hw, hpw⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_mem_etaPiece_smul_eq_of_smul_eq_nMap_quotient_of_inf_eq_bot
    p ι Φ ψ t ((algebraMap S (Localization.Away (a₀ * a₁))).comp g) hp0R hcR LR hLR j (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XS ((algebraMap S (Localization.Away (a₀ * a₁))).comp g)).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away (a₀ * a₁))).comp g)) hcR) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) hbca_res.2.2.1 hbca_res.2.2.2.1 z) (AddSubgroup.mem_inf.mpr ⟨hNz_eta, hNz_piece⟩) I₀ I₁ hI
    hcI₀ LI₀ hLI₀ hXI₀ hVI₀ hPI₀ zI₀ hzI₀ hdivI₀
    hcI₁ LI₁ hLI₁ hXI₁ hVI₁ hPI₁ zI₁ hzI₁ hdivI₁
  exact ⟨a₀ * a₁, hfx, hcR, LR, hLR, hXres, hbca_res.2.2.1, hbca_res.2.2.2.1, w, hw, hpw⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_smul_eq_nMap_nMap_quotient_localization_of_inf_eq_bot
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_smul_eq_nMap_nMap_quotient_localization_of_inf_eq_bot (solution)
