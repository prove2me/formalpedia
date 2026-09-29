-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_bijective_cartierModule_map_nsmul_eq_of_isEtaSection_iff_of_bijective_XS_awayHom_of_lieZero_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/e0db494e-d76e-52f1-b87e-a974d665ae6b

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_eq_of_forall_nMap_bcPhi_single_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_mem_etaPiece_nsmul_rigidNum_eq_etaRed_nVarpi_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_bijective_cartierModule_map_nsmul_eq_of_isEtaSection_iff_of_bijective_XS_awayHom_of_lieZero_le_ker
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace RhoCompat

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.SpecialFormal

variable {p : ℕ} [Fact p.Prime]

theorem nsmul_nMk {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (k : ℕ) (m m' : D.M) : k • D.nMk (m, m') = D.nMk (k • m, k • m') := by
  rw [← map_nsmul]; rfl

theorem nVarpi_nMk {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (m m' : D.M) : D.nVarpi (D.nMk (m, m')) = D.nMk (D.varpi m, D.varpi m') := rfl

theorem nMap_nVarpi {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (z : D.NMod) :
    D.nMap D' f hV hPi (D.nVarpi z) = D'.nVarpi (D.nMap D' f hV hPi z) := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [nVarpi_nMk, nMap_nMk, nMap_nMk, nVarpi_nMk, hPi, hPi]

theorem nMap_nVarpi_pow {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (n : ℕ) (z : D.NMod) :
    D.nMap D' f hV hPi (((D.nVarpi : D.NMod →ₗ[WittVector p B] D.NMod) ^ n) z) =
      ((D'.nVarpi : D'.NMod →ₗ[WittVector p B'] D'.NMod) ^ n) (D.nMap D' f hV hPi z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, nMap_nVarpi]

theorem nsmul_eq_zero_of_nMk_eq_zero {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p B j) (x : D.M) (hx : D.nMk (x, 0) = 0) : (p : ℕ) • x = 0 := by
  rw [nMk_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨y, hy⟩ := hx
  rw [nRelMap_apply, Prod.mk.injEq] at hy
  obtain ⟨hy1, hy2⟩ := hy
  have hPi : D.varpi (D.ofSigma y) = 0 := by
    have h2 : -D.varpi (D.ofSigma y) = 0 := D.toSigma.injective hy2
    exact neg_eq_zero.mp h2
  have hpy : (p : ℕ) • D.ofSigma y = 0 := by
    rw [← D.varpi_varpi, hPi, map_zero]
  rw [← hy1, ← map_nsmul, hpy, map_zero]

theorem p_nsmul_nMk {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p B j) (x x' : D.M) :
    (p : ℕ) • D.nMk (x, x') = D.nMk ((p : ℕ) • x + D.verschiebung (D.varpi x'), 0) := by
  have h1 : D.nMk (D.verschiebung (D.varpi x'), 0) = D.nMk (0, D.varpi (D.varpi x')) := by
    rw [← sub_zero (D.nMk (D.verschiebung (D.varpi x'), 0)),
      ← D.nMk_verschiebung_neg_varpi (D.varpi x'), ← map_sub, Prod.mk_sub_mk, sub_self,
      sub_neg_eq_add, zero_add]
  have h2 : ((p : ℕ) • x, D.varpi (D.varpi x')) = ((p : ℕ) • x, (0 : D.M)) + (0, D.varpi (D.varpi x')) := by
    rw [Prod.mk_add_mk, add_zero, zero_add]
  rw [nsmul_nMk, ← D.varpi_varpi x', h2, map_add, ← h1, ← map_add, Prod.mk_add_mk, add_zero]

theorem smul3 {M : Type} [AddCommMonoid M] (q a b : ℕ) (x : M) :
    q • (q ^ a • (q ^ b • x)) = q ^ (a + b + 1) • x := by
  rw [← mul_smul, ← mul_smul]
  congr 1
  ring

theorem nMap_comp_apply {B1 B2 B3 : Type} [CommRing B1] [CommRing B2] [CommRing B3]
    {j1 : Zp2 p →+* B1} {j2 : Zp2 p →+* B2} {j3 : Zp2 p →+* B3}
    (D1 : GradedCartierModuleData p B1 j1) (D2 : GradedCartierModuleData p B2 j2)
    (D3 : GradedCartierModuleData p B3 j3)
    (f : D1.M →+ D2.M) (hfV : ∀ x, f (D1.verschiebung x) = D2.verschiebung (f x))
    (hfPi : ∀ x, f (D1.varpi x) = D2.varpi (f x))
    (g : D2.M →+ D3.M) (hgV : ∀ x, g (D2.verschiebung x) = D3.verschiebung (g x))
    (hgPi : ∀ x, g (D2.varpi x) = D3.varpi (g x))
    (hcV : ∀ x, (g.comp f) (D1.verschiebung x) = D3.verschiebung ((g.comp f) x))
    (hcPi : ∀ x, (g.comp f) (D1.varpi x) = D3.varpi ((g.comp f) x)) (z : D1.NMod) :
    D1.nMap D3 (g.comp f) hcV hcPi z = D2.nMap D3 g hgV hgPi (D1.nMap D2 f hfV hfPi z) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D1.nMk_surjective z
  rw [nMap_nMk, nMap_nMk, nMap_nMk]
  rfl

theorem nMap_congr {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f g : D.M →+ D'.M) (hfg : ∀ x, f x = g x) (hV hPi hV' hPi') (z : D.NMod) :
    D.nMap D' f hV hPi z = D.nMap D' g hV' hPi' z := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D.nMk_surjective z
  rw [nMap_nMk, nMap_nMk, hfg, hfg]

theorem comp_compat {M1 M2 M3 : Type} [AddCommGroup M1] [AddCommGroup M2] [AddCommGroup M3]
    (f : M1 →+ M2) (g : M2 →+ M3) (V1 : M1 → M1) (V2 : M2 → M2) (V3 : M3 → M3)
    (hf : ∀ x, f (V1 x) = V2 (f x)) (hg : ∀ x, g (V2 x) = V3 (g x)) :
    ∀ x, (g.comp f) (V1 x) = V3 ((g.comp f) x) := fun x => by
  show g (f (V1 x)) = V3 (g (f x))
  rw [hf, hg]

section bc
variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T] {d : ℕ}

theorem bc_congr {Φ : MvFormalGroup d R} {Ψ : MvFormalGroup d S} [Φ.IsComm] [Ψ.IsComm]
    {f f' : R →+* S} (hff' : f = f') (h : Φ.map f = Ψ) (h' : Φ.map f' = Ψ) (m : CartierModule p Φ) :
    baseChangeEq (p := p) f h m = baseChangeEq f' h' m := by
  subst hff'; rfl

theorem bc_bc {Φ : MvFormalGroup d R} {Ψ : MvFormalGroup d S} {Χ : MvFormalGroup d T}
    [Φ.IsComm] [Ψ.IsComm] [Χ.IsComm]
    (f : R →+* S) (g : S →+* T) (e : R →+* T) (hgf : g.comp f = e)
    (h : Φ.map f = Ψ) (h' : Ψ.map g = Χ) (h'' : Φ.map e = Χ) (m : CartierModule p Φ) :
    baseChangeEq g h' (baseChangeEq f h m) = baseChangeEq e h'' m := by
  subst hgf; exact baseChangeEq_baseChangeEq f g h h' h'' m

theorem bc_bc_id {Φ : MvFormalGroup d R} {Ψ : MvFormalGroup d S} [Φ.IsComm] [Ψ.IsComm]
    (f : R →+* S) (g : S →+* R) (hgf : g.comp f = RingHom.id R)
    (h : Φ.map f = Ψ) (h' : Ψ.map g = Φ) (m : CartierModule p Φ) :
    baseChangeEq g h' (baseChangeEq f h m) = m := by
  rw [bc_bc f g (RingHom.id R) hgf h h' (map_ringHom_id' Φ) m]
  exact baseChangeEq_id _ m

theorem witt_map_map (f : R →+* S) (g : S →+* T) (w : WittVector p R) :
    WittVector.map g (WittVector.map f w) = WittVector.map (g.comp f) w := by
  ext n; simp only [WittVector.map_coeff, RingHom.comp_apply]

theorem witt_map_id' {f : R →+* R} (hf : f = RingHom.id R) (w : WittVector p R) :
    WittVector.map f w = w := by
  subst hf; ext n; simp only [WittVector.map_coeff, RingHom.id_apply]

theorem mvps_map_map_id {σ : Type} {f : R →+* S} {g : S →+* R} (hgf : g.comp f = RingHom.id R)
    (φ : MvPowerSeries σ R) : MvPowerSeries.map g (MvPowerSeries.map f φ) = φ := by
  rw [MvPowerSeries.map_map, hgf, MvPowerSeries.map_id]; rfl

end bc

end RhoCompat

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {κ : Type} [Field κ] [IsAlgClosed κ] [CharP κ p] [Algebra ℤ_[p] κ] (ψ : WittVector p k →+* κ)
    (t t' : Rigidified p Φ κ) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ)
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q) (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ ψ Q')
    (hiso : Q.IsIsomorphic Q')
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ) (hOD' : FormalODModule.IsODHom (t'.Φbar ψ) t'.Xbar t'.ρ)
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hc' : t'.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb' : t'.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : κ)))
    (L : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) (hL : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).IsCanonicalLMap L)
    (L' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').M →+ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) (hL' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').IsCanonicalLMap L')
    (i : Fin 2)
    (hi : ∀ m ∈ (t.XS (Rigidified.awayHom (1 : κ))).gradedPiece (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (i : ℕ), ∃ y : MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom (1 : κ))).F,
        MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct (t.XS (Rigidified.awayHom (1 : κ))).varpiEnd m)
    (hi' : ∀ m ∈ (t'.XS (Rigidified.awayHom (1 : κ))).gradedPiece (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (i : ℕ), ∃ y : MvFormalGroup.CartierModule p (t'.XS (Rigidified.awayHom (1 : κ))).F,
        MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct (t'.XS (Rigidified.awayHom (1 : κ))).varpiEnd m)
    (θη : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i →+ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i)
    (hcoord : ∀ (z : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i) (v : Fin 2 → ℚ_[p]),
        t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL i (z : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) v ↔
          t'.IsEtaSection ι hcΦ rΦ ψ hOD' (Rigidified.awayHom (1 : κ)) hc' hcb' hcΦg L' hL' i ((θη z : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) v)
    (Θ : MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom (1 : κ))).F →+ MvFormalGroup.CartierModule p (t'.XS (Rigidified.awayHom (1 : κ))).F) (hΘ : Function.Bijective Θ)
    (hΘF : ∀ f, Θ (MvFormalGroup.CartierModule.frobenius f) = MvFormalGroup.CartierModule.frobenius (Θ f))
    (hΘV : ∀ f, Θ (MvFormalGroup.CartierModule.verschiebungInt f) = MvFormalGroup.CartierModule.verschiebungInt (Θ f))
    (hΘW : ∀ (w : WittVector p (Rigidified.Baway (1 : κ))) f, Θ (w • f) = w • Θ f)
    (hΘa : ∀ (a : Zp2 p) f, Θ (MvFormalGroup.CartierModule.endAct ((t.XS (Rigidified.awayHom (1 : κ))).actEnd a) f) =
        MvFormalGroup.CartierModule.endAct ((t'.XS (Rigidified.awayHom (1 : κ))).actEnd a) (Θ f))
    (hΘPi : ∀ f, Θ (MvFormalGroup.CartierModule.endAct (t.XS (Rigidified.awayHom (1 : κ))).varpiEnd f) =
        MvFormalGroup.CartierModule.endAct (t'.XS (Rigidified.awayHom (1 : κ))).varpiEnd (Θ f))
    (hΘη : ∀ (m : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M) (hm : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0) ∈ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i),
        ((θη ⟨((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0), hm⟩ : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').nMk (Θ m, 0)) :
    ∃ (Ψ : MvFormalGroup 2 κ) (_ : Ψ.IsComm) (ρκ : Ψ.Hom t.X.F) (ρκ' : Ψ.Hom t'.X.F)
      (θ : MvFormalGroup.CartierModule p t.X.F →+ MvFormalGroup.CartierModule p t'.X.F),
      Series.map (Ideal.Quotient.mk (pIdeal p κ)) ρκ.toPowerSeries = t.ρ ∧
      Series.map (Ideal.Quotient.mk (pIdeal p κ)) ρκ'.toPowerSeries = t'.ρ ∧
      Function.Bijective θ ∧
      (∀ f, θ (MvFormalGroup.CartierModule.frobenius f) = MvFormalGroup.CartierModule.frobenius (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.verschiebung f) = MvFormalGroup.CartierModule.verschiebung (θ f)) ∧
      (∀ (a : κ) f, θ (MvFormalGroup.CartierModule.homothety a f) = MvFormalGroup.CartierModule.homothety a (θ f)) ∧
      (∀ (a : Zp2 p) f, θ (MvFormalGroup.CartierModule.endAct (t.X.actEnd a) f) =
        MvFormalGroup.CartierModule.endAct (t'.X.actEnd a) (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.endAct t.X.varpiEnd f) =
        MvFormalGroup.CartierModule.endAct t'.X.varpiEnd (θ f)) ∧
      ∃ c : ℕ, ∀ f : MvFormalGroup.CartierModule p Ψ,
        θ (MvFormalGroup.CartierModule.map ρκ (p ^ (c + t'.n) • f)) =
          MvFormalGroup.CartierModule.map ρκ' (p ^ (c + t.n) • f) := by
  classical

  have H1 : Submonoid.powers (1 : κ) ≤ IsUnit.submonoid κ := Submonoid.powers_le.2 isUnit_one
  let gA : κ →+* Rigidified.Baway (1 : κ) := Rigidified.awayHom (1 : κ)
  let E : κ ≃ₐ[κ] Rigidified.Baway (1 : κ) :=
    IsLocalization.atUnits κ (Submonoid.powers (1 : κ)) H1
  have hEg : ∀ x, E x = gA x := fun x => E.commutes x
  let hA : Rigidified.Baway (1 : κ) →+* κ := E.symm.toRingEquiv.toRingHom
  have hhg : hA.comp gA = RingHom.id κ := RingHom.ext fun x => by
    show E.symm (gA x) = x
    rw [← hEg, AlgEquiv.symm_apply_apply]
  have hgh : gA.comp hA = RingHom.id _ := RingHom.ext fun y => by
    show gA (E.symm y) = y
    rw [← hEg, AlgEquiv.apply_symm_apply]
  have hgx : ∀ x, hA (gA x) = x := fun x => RingHom.congr_fun hhg x
  have hhy : ∀ y, gA (hA y) = y := fun y => RingHom.congr_fun hgh y
  have hginj : Function.Injective gA := Function.LeftInverse.injective hgx
  have hhinj : Function.Injective hA := Function.LeftInverse.injective hhy
  have hpκ : (p : κ) = 0 := CharP.cast_eq_zero κ p
  have hpS : (p : Rigidified.Baway (1 : κ)) = 0 := by
    rw [← map_natCast gA p, hpκ, map_zero]
  have hbotκ : pIdeal p κ = ⊥ := Ideal.span_singleton_eq_bot.2 hpκ
  have hbotS : pIdeal p (Rigidified.Baway (1 : κ)) = ⊥ := Ideal.span_singleton_eq_bot.2 hpS
  let mkκ : κ →+* κ ⧸ pIdeal p κ := Ideal.Quotient.mk (pIdeal p κ)
  let mkS : Rigidified.Baway (1 : κ) →+* Rigidified.Baway (1 : κ) ⧸ pIdeal p (Rigidified.Baway (1 : κ)) :=
    Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : κ)))
  let Eκ : κ ⧸ pIdeal p κ ≃+* κ := (Ideal.quotEquivOfEq hbotκ).trans (RingEquiv.quotientBot κ)
  let s : κ ⧸ pIdeal p κ →+* κ := Eκ.toRingHom
  have hsmk : s.comp mkκ = RingHom.id κ := RingHom.ext fun x => by
    show RingEquiv.quotientBot κ (Ideal.quotEquivOfEq hbotκ (Ideal.Quotient.mk (pIdeal p κ) x)) = x
    rw [Ideal.quotEquivOfEq_mk, RingEquiv.quotientBot_mk]
  have hmks : mkκ.comp s = RingHom.id _ := RingHom.ext fun y => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    show mkκ ((s.comp mkκ) x) = mkκ x
    rw [hsmk]; rfl
  let ES : Rigidified.Baway (1 : κ) ⧸ pIdeal p (Rigidified.Baway (1 : κ)) ≃+* Rigidified.Baway (1 : κ) :=
    (Ideal.quotEquivOfEq hbotS).trans (RingEquiv.quotientBot _)
  let σ : Rigidified.Baway (1 : κ) ⧸ pIdeal p (Rigidified.Baway (1 : κ)) →+* Rigidified.Baway (1 : κ) :=
    ES.toRingHom
  have hσmk : σ.comp mkS = RingHom.id _ := RingHom.ext fun x => by
    show RingEquiv.quotientBot _ (Ideal.quotEquivOfEq hbotS (Ideal.Quotient.mk _ x)) = x
    rw [Ideal.quotEquivOfEq_mk, RingEquiv.quotientBot_mk]
  have hmkσ : mkS.comp σ = RingHom.id _ := RingHom.ext fun y => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    show mkS ((σ.comp mkS) x) = mkS x
    rw [hσmk]; rfl
  have hmkSinj : Function.Injective mkS := by
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker]; exact hbotS
  let e : κ →+* Rigidified.Baway (1 : κ) ⧸ pIdeal p (Rigidified.Baway (1 : κ)) := mkS.comp gA
  have he : e = (reduceMap gA).comp mkκ := RingHom.ext fun x => rfl
  have hes : e.comp s = reduceMap gA := by rw [he, RingHom.comp_assoc, hmks, RingHom.comp_id]
  have heh : e.comp hA = mkS := by
    show (mkS.comp gA).comp hA = mkS
    rw [RingHom.comp_assoc, hgh, RingHom.comp_id]
  have hσe : σ.comp e = gA := by
    show σ.comp (mkS.comp gA) = gA
    rw [← RingHom.comp_assoc, hσmk, RingHom.id_comp]
  have heinj : Function.Injective e := fun x y hxy => hginj (hmkSinj hxy)

  have hXh : (t.XS (Rigidified.awayHom (1 : κ))).F.map hA = t.X.F := by
    show (t.X.F.map gA).map hA = t.X.F
    rw [map_map_ringHom, hhg, map_ringHom_id']
  have hXh' : (t'.XS (Rigidified.awayHom (1 : κ))).F.map hA = t'.X.F := by
    show (t'.X.F.map gA).map hA = t'.X.F
    rw [map_map_ringHom, hhg, map_ringHom_id']
  have hXbs : t.Xbar.F.map s = t.X.F := by
    show (t.X.F.map mkκ).map s = t.X.F
    rw [map_map_ringHom, hsmk, map_ringHom_id']
  have hXbs' : t'.Xbar.F.map s = t'.X.F := by
    show (t'.X.F.map mkκ).map s = t'.X.F
    rw [map_map_ringHom, hsmk, map_ringHom_id']
  have hXe : t.X.F.map e = (t.XbarS (Rigidified.awayHom (1 : κ))).F := by
    show t.X.F.map e = (t.X.F.map mkκ).map (reduceMap gA)
    rw [map_map_ringHom, he]
  have hXe' : t'.X.F.map e = (t'.XbarS (Rigidified.awayHom (1 : κ))).F := by
    show t'.X.F.map e = (t'.X.F.map mkκ).map (reduceMap gA)
    rw [map_map_ringHom, he]
  have hXbσ : (t.XbarS (Rigidified.awayHom (1 : κ))).F.map σ = (t.XS (Rigidified.awayHom (1 : κ))).F := by
    show ((t.X.F.map mkκ).map (reduceMap gA)).map σ = t.X.F.map gA
    rw [map_map_ringHom, map_map_ringHom, RingHom.comp_assoc, ← he, hσe]
  let Ψ : MvFormalGroup 2 κ := (t.Φbar ψ).F.map s
  have hΨe : Ψ.map e = (Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).F := by
    show ((Φ.map (residueMap ψ)).F.map s).map e = (Φ.map (residueMap ψ)).F.map (reduceMap gA)
    rw [map_map_ringHom, hes]
  have hρs : IsLawHom Ψ t.X.F (t.ρ.map s) := by
    have h1 := hOD.1.map s
    rwa [hXbs] at h1
  have hρs' : IsLawHom Ψ t'.X.F (t'.ρ.map s) := by
    have h1 := hOD'.1.map s
    rwa [hXbs'] at h1
  let ρκ : Ψ.Hom t.X.F := hρs.toHom
  let ρκ' : Ψ.Hom t'.X.F := hρs'.toHom

  let bcg : CartierModule p t.X.F →+ CartierModule p (t.XS (Rigidified.awayHom (1 : κ))).F :=
    baseChangeEq gA rfl
  let bcg' : CartierModule p t'.X.F →+ CartierModule p (t'.XS (Rigidified.awayHom (1 : κ))).F :=
    baseChangeEq gA rfl
  let bch : CartierModule p (t.XS (Rigidified.awayHom (1 : κ))).F →+ CartierModule p t.X.F :=
    baseChangeEq hA hXh
  let bch' : CartierModule p (t'.XS (Rigidified.awayHom (1 : κ))).F →+ CartierModule p t'.X.F :=
    baseChangeEq hA hXh'
  let θ : CartierModule p t.X.F →+ CartierModule p t'.X.F := bch'.comp (Θ.comp bcg)
  let redinv : CartierModule p (t.XbarS (Rigidified.awayHom (1 : κ))).F →+
      CartierModule p (t.XS (Rigidified.awayHom (1 : κ))).F := baseChangeEq σ hXbσ
  have hredinv_red : ∀ u, redinv (t.redC (Rigidified.awayHom (1 : κ)) u) = u := fun u =>
    RhoCompat.bc_bc_id mkS σ hσmk (t.XS_F_map_mk _) hXbσ u
  let Θb : CartierModule p (t.XbarS (Rigidified.awayHom (1 : κ))).F →+
      CartierModule p (t'.XbarS (Rigidified.awayHom (1 : κ))).F :=
    (t'.redC (Rigidified.awayHom (1 : κ))).comp (Θ.comp redinv)
  let EX : CartierModule p t.X.F →+ CartierModule p (t.XbarS (Rigidified.awayHom (1 : κ))).F :=
    baseChangeEq e hXe
  let EX' : CartierModule p t'.X.F →+ CartierModule p (t'.XbarS (Rigidified.awayHom (1 : κ))).F :=
    baseChangeEq e hXe'
  let EΨ : CartierModule p Ψ →+ CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).F :=
    baseChangeEq e hΨe
  have hEX'inj : Function.Injective EX' := baseChangeEq_injective e hXe' heinj
  have hI1 : ∀ y, EX' (θ y) = Θb (EX y) := fun y => by
    show baseChangeEq e hXe' (baseChangeEq hA hXh' (Θ (baseChangeEq gA rfl y))) =
      baseChangeEq mkS (t'.XS_F_map_mk _) (Θ (baseChangeEq σ hXbσ (baseChangeEq e hXe y)))
    rw [RhoCompat.bc_bc hA e mkS heh hXh' hXe' (t'.XS_F_map_mk _),
      RhoCompat.bc_bc e σ gA hσe hXe hXbσ rfl]
    rfl
  have hI2 : ∀ u, EX (CartierModule.map ρκ u) =
      Rigidified.rhoC ψ t hOD.1 (Rigidified.awayHom (1 : κ)) (EΨ u) := fun u =>
    baseChangeEq_map e hΨe hXe (φ := ρκ)
      (ψ := (hOD.1.map (reduceMap gA)).toHom) (fun i => by
        show MvPowerSeries.map (reduceMap gA) (t.ρ i) = MvPowerSeries.map e (MvPowerSeries.map s (t.ρ i))
        rw [MvPowerSeries.map_map, hes]) u
  have hI2' : ∀ u, EX' (CartierModule.map ρκ' u) =
      Rigidified.rhoC ψ t' hOD'.1 (Rigidified.awayHom (1 : κ)) (EΨ u) := fun u =>
    baseChangeEq_map e hΨe hXe' (φ := ρκ')
      (ψ := (hOD'.1.map (reduceMap gA)).toHom) (fun i => by
        show MvPowerSeries.map (reduceMap gA) (t'.ρ i) = MvPowerSeries.map e (MvPowerSeries.map s (t'.ρ i))
        rw [MvPowerSeries.map_map, hes]) u

  have hΘV' : ∀ x, Θ (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).verschiebung x) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').verschiebung (Θ x) := hΘV
  have hΘPi' : ∀ x, Θ (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).varpi x) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').varpi (Θ x) := hΘPi
  have hriV : ∀ x, redinv (((t.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb).verschiebung x) = ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).verschiebung (redinv x) := fun x =>
    baseChangeEq_verschiebungInt σ hXbσ x
  have hriPi : ∀ x, redinv (((t.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb).varpi x) = ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).varpi (redinv x) := fun x =>
    baseChangeEq_endAct σ hXbσ (φ := (t.XbarS (Rigidified.awayHom (1 : κ))).varpiEnd)
      (ψ := (t.XS (Rigidified.awayHom (1 : κ))).varpiEnd) (fun i => by
        show MvPowerSeries.map gA (t.X.varpi i) =
          MvPowerSeries.map σ (MvPowerSeries.map (reduceMap gA) (MvPowerSeries.map mkκ (t.X.varpi i)))
        rw [MvPowerSeries.map_map, MvPowerSeries.map_map, RingHom.comp_assoc, ← he, hσe]) x
  have hrV := t.redC_verschiebungInt (Rigidified.awayHom (1 : κ))
  have hrPi := t.redC_endAct_varpiEnd (Rigidified.awayHom (1 : κ))
  have hrV' := t'.redC_verschiebungInt (Rigidified.awayHom (1 : κ))
  have hrPi' := t'.redC_endAct_varpiEnd (Rigidified.awayHom (1 : κ))
  have hΘrV : ∀ x, (Θ.comp redinv) (((t.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb).verschiebung x) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').verschiebung ((Θ.comp redinv) x) :=
    RhoCompat.comp_compat redinv Θ _ _ _ hriV hΘV'
  have hΘrPi : ∀ x, (Θ.comp redinv) (((t.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb).varpi x) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').varpi ((Θ.comp redinv) x) :=
    RhoCompat.comp_compat redinv Θ _ _ _ hriPi hΘPi'
  have hΘbV : ∀ x, Θb (((t.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb).verschiebung x) = ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb').verschiebung (Θb x) :=
    RhoCompat.comp_compat (Θ.comp redinv) (t'.redC _) _ _ _ hΘrV hrV'
  have hΘbPi : ∀ x, Θb (((t.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb).varpi x) = ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb').varpi (Θb x) :=
    RhoCompat.comp_compat (Θ.comp redinv) (t'.redC _) _ _ _ hΘrPi hrPi'
  have hΘbW : ∀ (w : WittVector p (Rigidified.Baway (1 : κ) ⧸ pIdeal p (Rigidified.Baway (1 : κ)))) x,
      Θb (w • x) = w • Θb x := fun w x => by
    show baseChangeEq mkS (t'.XS_F_map_mk _) (Θ (baseChangeEq σ hXbσ (w • x))) =
      w • baseChangeEq mkS (t'.XS_F_map_mk _) (Θ (baseChangeEq σ hXbσ x))
    rw [baseChangeEq_smul_witt, hΘW, baseChangeEq_smul_witt, RhoCompat.witt_map_map,
      RhoCompat.witt_map_id' hmkσ]

  let f₁ : CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).F →+
      CartierModule p (t'.XbarS (Rigidified.awayHom (1 : κ))).F :=
    Θb.comp (Rigidified.rhoC ψ t hOD.1 (Rigidified.awayHom (1 : κ)))
  let f₂ : CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).F →+
      CartierModule p (t'.XbarS (Rigidified.awayHom (1 : κ))).F :=
    Rigidified.rhoC ψ t' hOD'.1 (Rigidified.awayHom (1 : κ))
  have hρV := Rigidified.rhoC_verschiebungInt ψ t hOD.1 (Rigidified.awayHom (1 : κ))
  have hρPi := Rigidified.rhoC_endAct_varpiEnd ψ t hOD (Rigidified.awayHom (1 : κ))
  have hV₂ : ∀ x, f₂ (((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).verschiebung x) = ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb').verschiebung (f₂ x) :=
    Rigidified.rhoC_verschiebungInt ψ t' hOD'.1 (Rigidified.awayHom (1 : κ))
  have hPi₂ : ∀ x, f₂ (((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).varpi x) = ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb').varpi (f₂ x) :=
    Rigidified.rhoC_endAct_varpiEnd ψ t' hOD' (Rigidified.awayHom (1 : κ))
  have hV₁ : ∀ x, f₁ (((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).verschiebung x) = ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb').verschiebung (f₁ x) :=
    RhoCompat.comp_compat _ Θb _ _ _ hρV hΘbV
  have hPi₁ : ∀ x, f₁ (((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).varpi x) = ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb').varpi (f₁ x) :=
    RhoCompat.comp_compat _ Θb _ _ _ hρPi hΘbPi
  have hW₂ : ∀ (w : WittVector p (Rigidified.Baway (1 : κ) ⧸ pIdeal p (Rigidified.Baway (1 : κ)))) x,
      f₂ (w • x) = w • f₂ x := fun w x => by
    show Rigidified.rhoC ψ t' hOD'.1 _ (w • x) = _
    rw [Rigidified.rhoC, map_smul_witt]
  have hWρ : ∀ (w : WittVector p (Rigidified.Baway (1 : κ) ⧸ pIdeal p (Rigidified.Baway (1 : κ)))) x,
      Rigidified.rhoC ψ t hOD.1 (Rigidified.awayHom (1 : κ)) (w • x) =
        w • Rigidified.rhoC ψ t hOD.1 (Rigidified.awayHom (1 : κ)) x := fun w x => by
    rw [Rigidified.rhoC, map_smul_witt]
  have hW₁ : ∀ (w : WittVector p (Rigidified.Baway (1 : κ) ⧸ pIdeal p (Rigidified.Baway (1 : κ)))) x,
      f₁ (w • x) = w • f₁ x := fun w x => by
    show Θb (Rigidified.rhoC ψ t hOD.1 (Rigidified.awayHom (1 : κ)) (w • x)) =
      w • Θb (Rigidified.rhoC ψ t hOD.1 (Rigidified.awayHom (1 : κ)) x)
    rw [hWρ, hΘbW]

  let NΘ : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod →+ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod := ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMap ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc') Θ hΘV' hΘPi'
  let NΘb : ((t.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb).NMod →+ ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb').NMod := ((t.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb).nMap ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb') Θb hΘbV hΘbPi
  let Nρ : ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).NMod →+ ((t.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb).NMod := ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).nMap ((t.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb) (Rigidified.rhoC ψ t hOD.1 _) hρV hρPi
  let Nρ' : ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).NMod →+ ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb').NMod := ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).nMap ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb') f₂ hV₂ hPi₂
  let Nbc : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).NMod := (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg) (Rigidified.bcPhi (Φ := Φ) ψ (Rigidified.awayHom (1 : κ)))
    (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ _) (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ _)
  have hrig : ∀ w, t.rigidNum ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hcb hcΦg w = Nρ (Nbc (rΦ w)) :=
    fun w => rfl
  have hrig' : ∀ w, t'.rigidNum ι hcΦ rΦ ψ hOD' (Rigidified.awayHom (1 : κ)) hcb' hcΦg w = Nρ' (Nbc (rΦ w)) :=
    fun w => rfl
  have hNf₁ : ∀ z, ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).nMap ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb') f₁ hV₁ hPi₁ z = NΘb (Nρ z) := fun z =>
    RhoCompat.nMap_comp_apply ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg) ((t.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb) ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb') (Rigidified.rhoC ψ t hOD.1 _) hρV hρPi Θb hΘbV hΘbPi hV₁ hPi₁ z

  have hredΘ : ∀ x, ((t'.redC (Rigidified.awayHom (1 : κ))).comp Θ) x =
      (Θb.comp (t.redC (Rigidified.awayHom (1 : κ)))) x := fun x => by
    show t'.redC _ (Θ x) = t'.redC _ (Θ (redinv (t.redC _ x)))
    rw [hredinv_red]
  have hnat : ∀ z, t'.etaRed ι ψ (Rigidified.awayHom (1 : κ)) hc' hcb' (NΘ z) =
      NΘb (t.etaRed ι ψ (Rigidified.awayHom (1 : κ)) hc hcb z) := fun z => by
    show ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').nMap ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb') (t'.redC _) hrV' hrPi' (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMap ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc') Θ hΘV' hΘPi' z) =
      ((t.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb).nMap ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb') Θb hΘbV hΘbPi (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMap ((t.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb) (t.redC _) hrV hrPi z)
    rw [← RhoCompat.nMap_comp_apply ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc) ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc') ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb') Θ hΘV' hΘPi' (t'.redC _) hrV' hrPi'
        (RhoCompat.comp_compat Θ (t'.redC _) _ _ _ hΘV' hrV')
        (RhoCompat.comp_compat Θ (t'.redC _) _ _ _ hΘPi' hrPi'),
      ← RhoCompat.nMap_comp_apply ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc) ((t.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb) ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb') (t.redC _) hrV hrPi Θb hΘbV hΘbPi
        (RhoCompat.comp_compat (t.redC _) Θb _ _ _ hrV hΘbV)
        (RhoCompat.comp_compat (t.redC _) Θb _ _ _ hrPi hΘbPi)]
    exact RhoCompat.nMap_congr ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc) ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb') _ _ hredΘ _ _ _ _ z

  have hnil : IsNilpotent (p : κ) := ⟨1, by rw [pow_one]; exact hpκ⟩
  have H : ∀ w : Fin 2 → ℤ_[p], ∃ kf : ℕ,
      p ^ (kf + t'.n) • NΘb (Nρ (Nbc (rΦ w))) =
        p ^ (kf + t.n) • Nρ' (Nbc (rΦ w)) := by
    intro w
    have probe :=
      CerednikDrinfeld.SpecialFormal.Rigidified.exists_mem_etaPiece_nsmul_rigidNum_eq_etaRed_nVarpi_of_isAlgClosed
        p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ κ ψ hnil t ht hc hcb hcΦg L hL i w
    refine probe.elim fun N hN => hN.elim fun z hz2 => ?_
    have hzη := hz2.1
    have hz := hz2.2
    refine (GradedCartierModuleData.nMk_surjective _ z).elim fun xx hxz => ?_

    have hpz : p • z = ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (p • xx.1 + ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).verschiebung (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).varpi xx.2), 0) := by
      rw [← hxz]; exact RhoCompat.p_nsmul_nMk ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc) xx.1 xx.2
    have hmη : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (p • xx.1 + ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).verschiebung (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).varpi xx.2), 0) ∈
        ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i := by
      rw [← hpz]; exact AddSubgroup.nsmul_mem _ hzη p
    have hθη := hΘη (p • xx.1 + ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).verschiebung (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).varpi xx.2)) hmη
    have hNΘz : NΘ (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (p • xx.1 + ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).verschiebung (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).varpi xx.2), 0)) =
        ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').nMk (Θ (p • xx.1 + ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).verschiebung (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).varpi xx.2)), 0) := by
      show ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMap ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc') Θ hΘV' hΘPi' _ = _
      rw [nMap_nMk, map_zero]
      try rfl

    have hred : t.etaRed ι ψ (Rigidified.awayHom (1 : κ)) hc hcb
        (((((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nVarpi : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod →ₗ[WittVector p (Rigidified.Baway (1 : κ))] ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) ^ (i : ℕ))
          (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (p • xx.1 + ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).verschiebung (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).varpi xx.2), 0))) =
        p ^ (N + 1) • t.rigidNum ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hcb hcΦg w := by
      rw [← hpz, map_nsmul, map_nsmul, pow_succ', mul_smul]
      exact congrArg (fun u => p • u) hz.symm

    have hile : (i : ℕ) ≤ t.n + N + 1 := by have := i.is_lt; omega
    let v : Fin 2 → ℚ_[p] := (p : ℚ_[p]) ^ (t.n + N + 1 - (i : ℕ)) • fun j => ((w j : ℤ_[p]) : ℚ_[p])
    have hpv : (p : ℚ_[p]) ^ (i : ℕ) • v = fun j => (((p ^ (t.n + N + 1) • w) j : ℤ_[p]) : ℚ_[p]) := by
      funext j
      show (p : ℚ_[p]) ^ (i : ℕ) * ((p : ℚ_[p]) ^ (t.n + N + 1 - (i : ℕ)) * ((w j : ℤ_[p]) : ℚ_[p])) =
        (((p ^ (t.n + N + 1) • w) j : ℤ_[p]) : ℚ_[p])
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hile, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow,
        PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
    have hsec : t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL i
        (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (p • xx.1 + ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).verschiebung (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).varpi xx.2), 0)) v := by
      refine ⟨hmη, 0, 0, p ^ (t.n + N + 1) • w, ?_, ?_⟩
      · rw [pow_zero, one_smul, hpv]
      · rw [pow_zero, one_smul, zero_add, add_zero, hred, map_nsmul, ← mul_smul, ← pow_add, ← add_assoc]
    have hsec' := (hcoord ⟨_, hmη⟩ v).1 hsec
    refine hsec'.2.elim fun m₂ h3 => h3.elim fun k₂ h4 => h4.elim fun w₂ h5 => ?_
    have hv₂ := h5.1
    have hr₂ := h5.2

    have hw₂ : w₂ = p ^ (m₂ + (t.n + N + 1)) • w := by
      funext j
      apply PadicInt.ext
      have hj := congrFun hv₂ j
      rw [hpv] at hj
      rw [← hj]
      show (p : ℚ_[p]) ^ m₂ * (((p ^ (t.n + N + 1) • w) j : ℤ_[p]) : ℚ_[p]) =
        (((p ^ (m₂ + (t.n + N + 1)) • w) j : ℤ_[p]) : ℚ_[p])
      rw [Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_pow, Nat.cast_pow,
        PadicInt.coe_mul, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_pow, PadicInt.coe_natCast,
        ← mul_assoc, ← pow_add]
    rw [hw₂, map_nsmul, hθη, ← hNΘz, ← RhoCompat.nMap_nVarpi_pow, hnat, hred, map_nsmul,
      hrig, hrig', ← mul_smul, ← mul_smul, ← pow_add, ← pow_add] at hr₂
    refine ⟨k₂ + m₂ + N + 1, ?_⟩
    have e1 : k₂ + m₂ + N + 1 + t'.n = k₂ + t'.n + m₂ + (N + 1) := by omega
    have e2 : k₂ + m₂ + N + 1 + t.n = k₂ + (m₂ + (t.n + N + 1)) := by omega
    rw [e1, e2]
    exact hr₂.symm
  let kf : (Fin 2 → ℤ_[p]) → ℕ := fun w => (H w).choose
  have hkf : ∀ w, p ^ (kf w + t'.n) • NΘb (Nρ (Nbc (rΦ w))) = p ^ (kf w + t.n) • Nρ' (Nbc (rΦ w)) :=
    fun w => (H w).choose_spec
  let K : ℕ := ∑ j : Fin 2, kf (Pi.single j 1)
  have hle : ∀ i' : Fin 2, kf (Pi.single i' 1) ≤ K := fun i' =>
    Finset.single_le_sum (f := fun j : Fin 2 => kf (Pi.single j 1)) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i')
  have hgen : ∀ i' : Fin 2,
      p ^ (K + t'.n) • ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).nMap ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb') f₁ hV₁ hPi₁ (Nbc (rΦ (Pi.single i' 1))) =
        p ^ (K + t.n) • ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).nMap ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb') f₂ hV₂ hPi₂ (Nbc (rΦ (Pi.single i' 1))) := by
    intro i'
    refine (Nat.exists_eq_add_of_le (hle i')).elim fun d hd => ?_
    rw [hNf₁, hd, add_comm (kf (Pi.single i' 1)) d, add_assoc, add_assoc,
      pow_add p d (kf (Pi.single i' 1) + t'.n), pow_add p d (kf (Pi.single i' 1) + t.n),
      mul_smul, mul_smul, hkf (Pi.single i' 1)]

  have hNR :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_nMap_eq_of_forall_nMap_bcPhi_single_eq
      p k ι Φ hΦ hΦ4 hcΦ rΦ hrΦ ψ t' ht' (Rigidified.awayHom (1 : κ)) hcb' hcΦg f₁ f₂ hW₁ hW₂
      hV₁ hPi₁ hV₂ hPi₂ _ _ hgen
  refine hNR.elim fun a hN => ?_
  have hM : ∀ m : CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).F,
      p ^ (a + (K + t'.n) + 1) • Θb (Rigidified.rhoC ψ t hOD.1 (Rigidified.awayHom (1 : κ)) m) =
        p ^ (a + (K + t.n) + 1) • Rigidified.rhoC ψ t' hOD'.1 (Rigidified.awayHom (1 : κ)) m := by
    intro m
    have hz := hN (((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).nMk (m, 0))
    have h1 : ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).nMap ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb') f₁ hV₁ hPi₁ (((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).nMk (m, 0)) =
        ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb').nMk (Θb (Rigidified.rhoC ψ t hOD.1 (Rigidified.awayHom (1 : κ)) m), 0) := by
      rw [nMap_nMk, map_zero]
      try rfl
    have h2 : ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).nMap ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb') f₂ hV₂ hPi₂ (((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : κ))) hcΦg).nMk (m, 0)) =
        ((t'.XbarS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : κ))) hcb').nMk (Rigidified.rhoC ψ t' hOD'.1 (Rigidified.awayHom (1 : κ)) m, 0) := by
      rw [nMap_nMk, map_zero]
      try rfl
    rw [h1, h2, RhoCompat.nsmul_nMk, RhoCompat.nsmul_nMk, RhoCompat.nsmul_nMk, RhoCompat.nsmul_nMk,
      smul_zero, smul_zero, smul_zero, smul_zero, ← sub_eq_zero, ← map_sub, Prod.mk_sub_mk, sub_zero] at hz
    have h3 := RhoCompat.nsmul_eq_zero_of_nMk_eq_zero _ _ hz
    rw [smul_sub, sub_eq_zero, RhoCompat.smul3, RhoCompat.smul3] at h3
    exact h3

  refine ⟨Ψ, inferInstance, ρκ, ρκ', θ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, a + K + 1, ?_⟩
  · show (t.ρ.map s).map mkκ = t.ρ
    rw [Series.map_map, hmks, Series.map_ringHom_id]
  · show (t'.ρ.map s).map mkκ = t'.ρ
    rw [Series.map_map, hmks, Series.map_ringHom_id]
  · refine ⟨fun x y hxy => ?_, fun y' => ?_⟩
    · exact baseChangeEq_injective gA rfl hginj (hΘ.1 (baseChangeEq_injective hA hXh' hhinj hxy))
    · refine (hΘ.2 (bcg' y')).elim fun u hu => ?_
      refine ⟨bch u, ?_⟩
      show bch' (Θ (bcg (bch u))) = y'
      rw [show bcg (bch u) = u from RhoCompat.bc_bc_id hA gA hgh hXh rfl u, hu]
      exact RhoCompat.bc_bc_id gA hA hhg rfl hXh' y'
  · intro f
    show bch' (Θ (bcg (frobenius f))) = frobenius (bch' (Θ (bcg f)))
    rw [baseChangeEq_frobenius, hΘF, baseChangeEq_frobenius]
  · intro f
    show bch' (Θ (bcg (verschiebung f))) = verschiebung (bch' (Θ (bcg f)))
    rw [← verschiebungInt_apply_eq_verschiebung, ← verschiebungInt_apply_eq_verschiebung,
      baseChangeEq_verschiebungInt, hΘV, baseChangeEq_verschiebungInt]
  · intro a' f
    show bch' (Θ (bcg (homothety a' f))) = homothety a' (bch' (Θ (bcg f)))
    rw [← teichmuller_smul, ← teichmuller_smul, baseChangeEq_smul_witt, hΘW, baseChangeEq_smul_witt,
      RhoCompat.witt_map_map, RhoCompat.witt_map_id' hhg]
  · intro a' f
    show bch' (Θ (bcg (endAct (t.X.actEnd a') f))) = endAct (t'.X.actEnd a') (bch' (Θ (bcg f)))
    rw [baseChangeEq_endAct gA _ (φ := t.X.actEnd a')
        (ψ := (t.XS (Rigidified.awayHom (1 : κ))).actEnd a') (fun _ => rfl), hΘa,
      baseChangeEq_endAct hA hXh' (φ := (t'.XS (Rigidified.awayHom (1 : κ))).actEnd a')
        (ψ := t'.X.actEnd a') (fun i => by
          show (t'.X.act a') i = MvPowerSeries.map hA (MvPowerSeries.map gA ((t'.X.act a') i))
          rw [RhoCompat.mvps_map_map_id hhg])]
  · intro f
    show bch' (Θ (bcg (endAct t.X.varpiEnd f))) = endAct t'.X.varpiEnd (bch' (Θ (bcg f)))
    rw [baseChangeEq_endAct gA _ (φ := t.X.varpiEnd)
        (ψ := (t.XS (Rigidified.awayHom (1 : κ))).varpiEnd) (fun _ => rfl), hΘPi,
      baseChangeEq_endAct hA hXh' (φ := (t'.XS (Rigidified.awayHom (1 : κ))).varpiEnd)
        (ψ := t'.X.varpiEnd) (fun i => by
          show t'.X.varpi i = MvPowerSeries.map hA (MvPowerSeries.map gA (t'.X.varpi i))
          rw [RhoCompat.mvps_map_map_id hhg])]
  · intro f
    apply hEX'inj
    have e1 : a + K + 1 + t'.n = a + (K + t'.n) + 1 := by omega
    have e2 : a + K + 1 + t.n = a + (K + t.n) + 1 := by omega
    rw [e1, e2]
    simp only [map_nsmul]
    rw [hI1, hI2, hI2']
    exact hM (EΨ f)

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_bijective_cartierModule_map_nsmul_eq_of_isEtaSection_iff_of_bijective_XS_awayHom_of_lieZero_le_ker
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_bijective_cartierModule_map_nsmul_eq_of_isEtaSection_iff_of_bijective_XS_awayHom_of_lieZero_le_ker (solution)
