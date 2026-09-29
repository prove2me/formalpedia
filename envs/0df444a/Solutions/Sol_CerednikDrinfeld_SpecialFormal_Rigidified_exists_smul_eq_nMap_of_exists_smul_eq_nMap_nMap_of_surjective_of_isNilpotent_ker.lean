-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_exists_smul_eq_nMap_nMap_of_surjective_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/944de4d0-d08c-57c8-8b40-adad85e67609

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

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_exists_smul_eq_nMap_nMap_of_surjective_of_isNilpotent_ker
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace RedReduceKit

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

end RedReduceKit

open RedReduceKit CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B)
    (i : Fin 2) (f : B) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
    (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M →+ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (z : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung i)
    (x : PrimeSpectrum B)

    {S : Type} [CommRing S] (q : Rigidified.Baway f →+* S) (hq : Function.Surjective q) (hqI : IsNilpotent (RingHom.ker q))
    (hcS : t.IsGradedS ι ψ (q.comp (Rigidified.awayHom f)))
    (LS : ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).M →+ ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).NMod) (hLS : ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).IsCanonicalLMap LS)
    (hXS : (t.XS (Rigidified.awayHom f)).F.map q = (t.XS (q.comp (Rigidified.awayHom f))).F)
    (hSV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXS (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXS m))
    (hSP : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXS (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXS m))
    (xS : PrimeSpectrum S) (hxS : Ideal.comap (q.comp (Rigidified.awayHom f)) xS.asIdeal = x.asIdeal)

    (hred : ∃ (f₀' : S) (_ : f₀' ∉ xS.asIdeal) (hc₀' : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f))))
      (L₀' : ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').M →+ ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').NMod) (hL₀' : ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').IsCanonicalLMap L₀')
      (hXr' : (t.XS (q.comp (Rigidified.awayHom f))).F.map (algebraMap S (Localization.Away f₀')) = (t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).F)
      (hrV' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr' (((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).verschiebung m) =
        ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr' m))
      (hrPi' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr' (((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).varpi m) =
        ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr' m))
      (z₀' : ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').NMod),
      z₀' ∈ ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').etaPiece L₀' hL₀'.isCartierLMap.map_verschiebung i ∧
        p • z₀' = ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).nMap ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀') (MvFormalGroup.CartierModule.baseChangeEq _ hXr') hrV' hrPi'
          (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).nMap ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS) (MvFormalGroup.CartierModule.baseChangeEq _ hXS) hSV hSP z)) :
    ∃ (f₀ : B) (_ : f₀ ∉ x.asIdeal) (hc₀ : t.IsGradedS ι ψ (Rigidified.awayHom (f * f₀)))
      (L₀ : ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).M →+ ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
      (hXr : (t.XS (Rigidified.awayHom f)).F.map (IsLocalization.Away.awayToAwayRight f f₀ : Rigidified.Baway f →+* Rigidified.Baway (f * f₀)) = (t.XS (Rigidified.awayHom (f * f₀))).F)
      (hrV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).verschiebung m) =
        ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (hrPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).varpi m) =
        ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (z₀ : ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).NMod),
      z₀ ∈ ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung i ∧
        p • z₀ = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).nMap ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXr) hrV hrPi z := by
  classical
  obtain ⟨f₀', hf₀', hc₀', L₀', hL₀', hXr', hrV', hrPi', z₀', hz₀', hdiv'⟩ := hred
  have hpBf : IsNilpotent ((p : ℕ) : Rigidified.Baway f) := by
    simpa only [map_natCast] using hB.map (Rigidified.awayHom f)
  have hpS : IsNilpotent ((p : ℕ) : S) := by
    simpa only [map_natCast] using hpBf.map q
  have hpT : IsNilpotent ((p : ℕ) : Localization.Away f₀') := by
    simpa only [map_natCast] using hpS.map (algebraMap S (Localization.Away f₀'))

  obtain ⟨a', ha'⟩ := hq f₀'
  obtain ⟨⟨a, sf⟩, has⟩ := IsLocalization.surj (Submonoid.powers f) a'
  obtain ⟨n, hn⟩ := sf.2
  have hn' : f ^ n = ↑sf := hn
  have has' : a' * Rigidified.awayHom f f ^ n = Rigidified.awayHom f a := by
    rw [← map_pow, hn']; exact has
  have hfu : IsUnit (Rigidified.awayHom f f) := IsLocalization.Away.algebraMap_isUnit f

  have ha_x : a ∉ x.asIdeal := by
    intro hax
    have h1 : (q.comp (Rigidified.awayHom f)) a ∈ xS.asIdeal := by
      rw [← hxS] at hax; exact hax
    have h2 : f₀' * q (Rigidified.awayHom f f) ^ n ∈ xS.asIdeal := by
      rw [← ha', ← map_pow, ← map_mul, has']; exact h1
    rcases xS.isPrime.mem_or_mem h2 with h3 | h3
    · exact hf₀' h3
    · exact xS.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h3 ((hfu.map q).pow n))

  have hpR : IsNilpotent ((p : ℕ) : Rigidified.Baway (f * a)) := by
    simpa only [map_natCast] using hB.map (Rigidified.awayHom (f * a))
  have hres : (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)).comp (Rigidified.awayHom f) = Rigidified.awayHom (f * a) :=
    IsLocalization.Away.lift_comp _ _
  have hres_apply : ∀ b : B, (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) (Rigidified.awayHom f b) = Rigidified.awayHom (f * a) b := fun b => IsLocalization.Away.awayToAwayRight_eq f a b
  have hfaU : IsUnit (Rigidified.awayHom (f * a) (f * a)) := IsLocalization.Away.algebraMap_isUnit (f * a)
  have haR : IsUnit (Rigidified.awayHom (f * a) a) := by
    rw [map_mul] at hfaU; exact isUnit_of_mul_isUnit_right hfaU
  have ha'R : IsUnit ((IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) a') := by
    have h := congrArg (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) has'
    rw [map_mul, map_pow, hres_apply, hres_apply] at h
    exact isUnit_of_mul_isUnit_left (h ▸ haR)

  have hT₀ : IsUnit (algebraMap S (Localization.Away f₀') f₀') := IsLocalization.Away.algebraMap_isUnit f₀'
  have hunit : IsUnit (((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f))) (f * a)) := by
    rw [map_mul]
    refine IsUnit.mul ?_ ?_
    · exact (hfu.map q).map (algebraMap S (Localization.Away f₀'))
    · show IsUnit (algebraMap S (Localization.Away f₀') (q (Rigidified.awayHom f a)))
      rw [← has', map_mul, ha', map_mul]
      exact hT₀.mul (((hfu.pow n).map q).map _)
  obtain ⟨θ, hθ⟩ : ∃ θ : Rigidified.Baway (f * a) →+* Localization.Away f₀', θ.comp (Rigidified.awayHom (f * a)) = (algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)) :=
    ⟨IsLocalization.Away.lift (f * a) hunit, IsLocalization.Away.lift_comp _ _⟩
  have hθ_apply : ∀ b : B, θ (Rigidified.awayHom (f * a) b) = algebraMap S (Localization.Away f₀') (q (Rigidified.awayHom f b)) := fun b => RingHom.congr_fun hθ b
  have hθres : θ.comp (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) = (algebraMap S (Localization.Away f₀')).comp q := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    rw [RingHom.comp_assoc, RingHom.comp_assoc]
    show θ.comp ((IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)).comp (Rigidified.awayHom f)) = (algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f))
    rw [hres, hθ]
  have hθres_apply : ∀ c : Rigidified.Baway f, θ ((IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) c) = algebraMap S (Localization.Away f₀') (q c) := fun c => RingHom.congr_fun hθres c
  have hθa' : θ ((IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) a') = algebraMap S (Localization.Away f₀') f₀' := by rw [hθres_apply, ha']

  have hθsurj : Function.Surjective θ := by
    intro tt
    obtain ⟨⟨s, sm⟩, hst⟩ := IsLocalization.surj (Submonoid.powers f₀') tt
    obtain ⟨m, hm⟩ := sm.2
    obtain ⟨c, rfl⟩ := hq s
    have hst' : tt * algebraMap S (Localization.Away f₀') f₀' ^ m = algebraMap S (Localization.Away f₀') (q c) := by
      have hm' : f₀' ^ m = ↑sm := hm
      rw [← map_pow, hm']; exact hst
    obtain ⟨u, hu⟩ := ha'R
    have hθu : θ ↑u = algebraMap S (Localization.Away f₀') f₀' := by rw [hu, hθa']
    refine ⟨(IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) c * ↑(u⁻¹ ^ m), ?_⟩
    have hinv : algebraMap S (Localization.Away f₀') f₀' ^ m * θ ↑(u⁻¹ ^ m) = 1 := by
      rw [← hθu, ← map_pow, ← map_mul, inv_pow, ← Units.val_pow_eq_pow_val, Units.mul_inv, map_one]
    rw [map_mul, hθres_apply, ← hst', mul_assoc, hinv, mul_one]

  have hkerle : RingHom.ker θ ≤ (RingHom.ker q).map (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) := by
    intro r hr
    obtain ⟨⟨b, sr⟩, hbr⟩ := IsLocalization.surj (Submonoid.powers (f * a)) r
    obtain ⟨k, hk⟩ := sr.2

    have hbr' : r * Rigidified.awayHom (f * a) (f * a) ^ k = Rigidified.awayHom (f * a) b := by
      have hk' : (f * a) ^ k = ↑sr := hk
      rw [← map_pow, hk']; exact hbr
    have hθb : θ (Rigidified.awayHom (f * a) b) = 0 := by
      rw [← hbr', map_mul, (RingHom.mem_ker).mp hr, zero_mul]
    rw [hθ_apply, IsLocalization.map_eq_zero_iff (Submonoid.powers f₀')] at hθb
    obtain ⟨⟨e, he⟩, hme⟩ := hθb
    obtain ⟨m, rfl⟩ := he

    have hmem : a' ^ m * Rigidified.awayHom f b ∈ RingHom.ker q := by
      rw [RingHom.mem_ker, map_mul, map_pow, ha']; exact hme
    have h1 : (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) (a' ^ m * Rigidified.awayHom f b) ∈ (RingHom.ker q).map (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) := Ideal.mem_map_of_mem _ hmem
    rw [map_mul, map_pow, hres_apply] at h1

    obtain ⟨v, hv⟩ := (ha'R.pow m)
    have h2 : Rigidified.awayHom (f * a) b ∈ (RingHom.ker q).map (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) := by
      have := Ideal.mul_mem_left _ (↑v⁻¹ : Rigidified.Baway (f * a)) h1
      rwa [← mul_assoc, ← hv, Units.inv_mul, one_mul] at this
    obtain ⟨w, hw⟩ := (hfaU.pow k)
    have h3 : r = Rigidified.awayHom (f * a) b * ↑w⁻¹ := by
      rw [← hbr', ← hw, mul_assoc, Units.mul_inv, mul_one]
    rw [h3]
    exact Ideal.mul_mem_right _ _ h2
  have hkerNil : IsNilpotent (RingHom.ker θ) := by
    obtain ⟨N, hN⟩ := hqI
    refine ⟨N, ?_⟩
    rw [Ideal.zero_eq_bot]
    apply le_bot_iff.mp
    calc RingHom.ker θ ^ N ≤ ((RingHom.ker q).map (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a))) ^ N := Ideal.pow_right_mono hkerle N
      _ = ⊥ := by rw [← Ideal.map_pow, hN, Ideal.zero_eq_bot, Ideal.map_bot]
  have hkerp : ∃ b : ℕ, ∀ r ∈ RingHom.ker θ, ((p : ℕ) : Rigidified.Baway (f * a)) ^ b * r = 0 := by
    obtain ⟨b, hb⟩ := hpR
    exact ⟨b, fun r _ => by rw [hb, zero_mul]⟩

  have hcR : t.IsGradedS ι ψ (Rigidified.awayHom (f * a)) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpR _

  have hXres : (t.XS (Rigidified.awayHom f)).F.map (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) = (t.XS (Rigidified.awayHom (f * a))).F := by
    show (t.X.F.map (Rigidified.awayHom f)).map _ = t.X.F.map (Rigidified.awayHom (f * a))
    rw [MvFormalGroup.map_map_ringHom, hres]
  have hXθ : (t.XS (Rigidified.awayHom (f * a))).F.map θ = (t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).F := by
    show (t.X.F.map (Rigidified.awayHom (f * a))).map θ = t.X.F.map ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))
    rw [MvFormalGroup.map_map_ringHom, hθ]
  have hXm_res : (t.XS (Rigidified.awayHom f)).map (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) = t.XS (Rigidified.awayHom (f * a)) := by
    rw [Rigidified.XS, Rigidified.XS, FormalODModule.map_map, hres]
  have hXm_θ : (t.XS (Rigidified.awayHom (f * a))).map θ = t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f))) := by
    rw [Rigidified.XS, Rigidified.XS, FormalODModule.map_map, hθ]
  have hj_res : (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)).comp (Rigidified.jS ι ψ (Rigidified.awayHom f)) = Rigidified.jS ι ψ (Rigidified.awayHom (f * a)) := by
    show (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)).comp ((Rigidified.awayHom f).comp (structureMap ι ψ)) = (Rigidified.awayHom (f * a)).comp (structureMap ι ψ)
    rw [← RingHom.comp_assoc, hres]
  have hj_θ : θ.comp (Rigidified.jS ι ψ (Rigidified.awayHom (f * a))) = Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f))) := by
    show θ.comp ((Rigidified.awayHom (f * a)).comp (structureMap ι ψ)) = ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f))).comp (structureMap ι ψ)
    rw [← RingHom.comp_assoc, hθ]

  obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL.exists_lift
  obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
  have hγ : (t.XS (Rigidified.awayHom f)).IsHomogeneousVBasis (Rigidified.jS ι ψ (Rigidified.awayHom f)) (fun k => fl (γl k)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData p _ _ hc _ hγf
  have hbca_res : IsBaseChangeAlong' (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc) ((t.XS (Rigidified.awayHom (f * a))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (f * a))) hcR) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXm_res _ hj_res hcR hXres
  have hγR := isHomogeneousVBasis_push (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) (t.XS (Rigidified.awayHom f)) (t.XS (Rigidified.awayHom (f * a))) hc hcR hXres _ hγ hbca_res
  have hbca_θ : IsBaseChangeAlong' θ ((t.XS (Rigidified.awayHom (f * a))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (f * a))) hcR) ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))) hc₀') (MvFormalGroup.CartierModule.baseChangeEq _ hXθ) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγR hcR _ hXm_θ _ hj_θ hc₀' hXθ
  have hγT := isHomogeneousVBasis_push θ (t.XS (Rigidified.awayHom (f * a))) (t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))) hcR hc₀' hXθ _ hγR hbca_θ

  have hD := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ hc).2
  have hDR := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγR hcR).2
  have hDT := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγT hc₀').2
  obtain ⟨LR, hLR⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (Rigidified.jS ι ψ (Rigidified.awayHom (f * a))) (isHausdorff_of_isNilpotent hpR) _ _ hγR hcR
  have hLL_res := natL_of_eq _ _ hpBf hpR _ hD _ hj_res _ hDR _ hbca_res L hL LR hLR
  have hLL_θ := natL_of_eq _ _ hpR hpT _ hDR _ hj_θ _ hDT _ hbca_θ LR hLR L₀' hL₀'

  have hbij := redInv_of_eq _ _ hθsurj hkerNil hkerp _ hDR _ hj_θ _ hDT _ hbca_θ LR hLR L₀' hL₀' hLL_θ

  have hzE := (AddSubgroup.mem_inf.mp hz).1
  have hzP := (AddSubgroup.mem_inf.mp hz).2
  have hNz_eta := nMap_mem_eta _ _ _ hbca_res.2.2.1 hbca_res.2.2.2.1 L hL.isCartierLMap.map_verschiebung LR hLR.isCartierLMap.map_verschiebung hLL_res z hzE
  have hNz_piece := nMap_mem_nPiece _ _ _ hbca_res.2.2.1 hbca_res.2.2.2.1 hbca_res.2.2.2.2.1 i z hzP

  have hz₀'E := (AddSubgroup.mem_inf.mp hz₀').1
  obtain ⟨w, hw, hNw⟩ := hbij.surjOn hz₀'E

  have hsq : ∀ m : MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom f)).F,
      MvFormalGroup.CartierModule.baseChangeEq θ hXθ (MvFormalGroup.CartierModule.baseChangeEq _ hXres m) =
      MvFormalGroup.CartierModule.baseChangeEq _ hXr' (MvFormalGroup.CartierModule.baseChangeEq _ hXS m) := by
    intro m
    apply MvFormalGroup.CartierModule.ext
    funext k
    show MvPowerSeries.map θ (MvPowerSeries.map (IsLocalization.Away.awayToAwayRight f a : Rigidified.Baway f →+* Rigidified.Baway (f * a)) (m.toPowerSeries k)) =
      MvPowerSeries.map (algebraMap S (Localization.Away f₀')) (MvPowerSeries.map q (m.toPowerSeries k))
    rw [MvPowerSeries.map_map, MvPowerSeries.map_map, hθres]

  have hkV : ∀ m, ((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).verschiebung m) = ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))) hc₀').verschiebung (((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) m) := fun m =>
    (congrArg (MvFormalGroup.CartierModule.baseChangeEq θ hXθ) (hbca_res.2.2.1 m)).trans (hbca_θ.2.2.1 _)
  have hkP : ∀ m, ((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).varpi m) = ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))) hc₀').varpi (((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) m) := fun m =>
    (congrArg (MvFormalGroup.CartierModule.baseChangeEq θ hXθ) (hbca_res.2.2.2.1 m)).trans (hbca_θ.2.2.2.1 _)
  have hdiv'' : p • z₀' = ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData (Rigidified.jS ι ψ (q.comp (Rigidified.awayHom f))) hcS).nMap ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))) hc₀') (MvFormalGroup.CartierModule.baseChangeEq _ hXr') hrV' hrPi'
      (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).nMap ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData (Rigidified.jS ι ψ (q.comp (Rigidified.awayHom f))) hcS) (MvFormalGroup.CartierModule.baseChangeEq _ hXS) hSV hSP z) := hdiv'
  have e1 : ((t.XS (Rigidified.awayHom (f * a))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (f * a))) hcR).nMap ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))) hc₀') (MvFormalGroup.CartierModule.baseChangeEq θ hXθ) hbca_θ.2.2.1 hbca_θ.2.2.2.1
        (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).nMap ((t.XS (Rigidified.awayHom (f * a))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (f * a))) hcR) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) hbca_res.2.2.1 hbca_res.2.2.2.1 z) =
      ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))) hc₀') ((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) hkV hkP z :=
    nMap_nMap_eq ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc) ((t.XS (Rigidified.awayHom (f * a))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (f * a))) hcR) ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))) hc₀') (MvFormalGroup.CartierModule.baseChangeEq _ hXres) hbca_res.2.2.1 hbca_res.2.2.2.1
      (MvFormalGroup.CartierModule.baseChangeEq θ hXθ) hbca_θ.2.2.1 hbca_θ.2.2.2.1 ((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) hkV hkP (fun _ => rfl) z
  have e2 : ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData (Rigidified.jS ι ψ (q.comp (Rigidified.awayHom f))) hcS).nMap ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))) hc₀') (MvFormalGroup.CartierModule.baseChangeEq _ hXr') hrV' hrPi'
        (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).nMap ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData (Rigidified.jS ι ψ (q.comp (Rigidified.awayHom f))) hcS) (MvFormalGroup.CartierModule.baseChangeEq _ hXS) hSV hSP z) =
      ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))) hc₀') ((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) hkV hkP z :=
    nMap_nMap_eq ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc) ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData (Rigidified.jS ι ψ (q.comp (Rigidified.awayHom f))) hcS) ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))) hc₀') (MvFormalGroup.CartierModule.baseChangeEq _ hXS) hSV hSP
      (MvFormalGroup.CartierModule.baseChangeEq _ hXr') hrV' hrPi' ((MvFormalGroup.CartierModule.baseChangeEq θ hXθ).comp (MvFormalGroup.CartierModule.baseChangeEq _ hXres)) hkV hkP (fun m => (hsq m).symm) z
  have hkey : ((t.XS (Rigidified.awayHom (f * a))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (f * a))) hcR).nMap ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))) hc₀') (MvFormalGroup.CartierModule.baseChangeEq θ hXθ) hbca_θ.2.2.1 hbca_θ.2.2.2.1 (p • w) =
      ((t.XS (Rigidified.awayHom (f * a))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (f * a))) hcR).nMap ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))) hc₀') (MvFormalGroup.CartierModule.baseChangeEq θ hXθ) hbca_θ.2.2.1 hbca_θ.2.2.2.1
        (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).nMap ((t.XS (Rigidified.awayHom (f * a))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (f * a))) hcR) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) hbca_res.2.2.1 hbca_res.2.2.2.1 z) := by
    rw [map_nsmul, hNw, hdiv'', e2, e1]
  have hpw : p • w = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).nMap ((t.XS (Rigidified.awayHom (f * a))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (f * a))) hcR) (MvFormalGroup.CartierModule.baseChangeEq _ hXres) hbca_res.2.2.1 hbca_res.2.2.2.1 z :=
    hbij.injOn (AddSubgroup.nsmul_mem _ hw p) hNz_eta hkey

  obtain ⟨w', hw', hpw'⟩ := exists_mem_etaPiece_nsmul_eq _ LR hLR i _ w hNz_piece hw p hpw
  exact ⟨a, ha_x, hcR, LR, hLR, hXres, hbca_res.2.2.1, hbca_res.2.2.2.1, w', hw', hpw'⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_exists_smul_eq_nMap_nMap_of_surjective_of_isNilpotent_ker
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_exists_smul_eq_nMap_nMap_of_surjective_of_isNilpotent_ker (solution)
