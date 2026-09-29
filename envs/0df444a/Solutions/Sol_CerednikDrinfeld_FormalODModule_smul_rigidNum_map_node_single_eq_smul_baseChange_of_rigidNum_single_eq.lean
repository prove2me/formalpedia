-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.smul_rigidNum_map_node_single_eq_smul_baseChange_of_rigidNum_single_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/31a5014e-cecf-5a04-a8ab-51f352cafc0f

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_smul_rigidNum_map_node_single_eq_smul_baseChange_of_rigidNum_single_eq

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

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

theorem bc_bc' {Φ : MvFormalGroup d R} {Ψ : MvFormalGroup d S} {Χ : MvFormalGroup d T}
    [Φ.IsComm] [Ψ.IsComm] [Χ.IsComm]
    (f : R →+* S) (g : S →+* T) (h : Φ.map f = Ψ) (h' : Ψ.map g = Χ) (m : CartierModule p Φ) :
    baseChangeEq g h' (baseChangeEq f h m) =
      baseChangeEq (g.comp f) (by rw [← map_map_ringHom, h, h']) m :=
  baseChangeEq_baseChangeEq f g h h' _ m

end bc

theorem vec2_map {α β : Type} (f : α → β) (a b : α) (i : Fin 2) : f (![a, b] i) = ![f a, f b] i := by
  fin_cases i <;> rfl

end RhoCompat

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
open CerednikDrinfeld.GradedCartierModuleData in
theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
(g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
(hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
(X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (γ : Fin 2 → CartierModule p X.F)
(hγ : X.IsHomogeneousVBasis (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) γ)
(hγa : X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k))))
(hXs : X.IsSpecial (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (hX4 : X.HasHeight 4)

(f₀ : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ : f₀.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ξ : f₀ (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0) (hf₀η : f₀ (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0)
(m : ℕ) (ρ₀ : Series (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hρ₀ : FormalODModule.IsIsogenyOfHeight Φ (X.map f₀) ρ₀ (4 * m))
(hOD₀ : FormalODModule.IsODHom (Rigidified.Φbar (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.Xbar (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.ρ (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))))
(hcb : Rigidified.IsGradedSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
(hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
(a : ℕ)
(hN : ∀ i : Fin 2,
    p ^ a • (Rigidified.rigidNum ι hcΦ rΦ (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) hcb hcΦg) (Pi.single i 1) =
      p ^ (a + m) • (![((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))), 0),
          ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nVarpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))), 0))] i))
    (S : Type) [CommRing S] (y₀ : (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* S) {S' : Type} [CommRing S'] (gS : S →+* S')
    (hOD' : FormalODModule.IsODHom (Rigidified.Φbar (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀)) (Rigidified.Xbar ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀)) (Rigidified.ρ ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀)))
    (hcb' : Rigidified.IsGradedSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) gS)
    (hcΦg' : Rigidified.IsGradedPhiS (Φ := Φ) ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) :
    ∀ i : Fin 2,
      p ^ a • Rigidified.rigidNum ι hcΦ rΦ (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) hOD' gS hcb' hcΦg' (Pi.single i 1) =
        p ^ (a + m) • (![((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb').nMk (baseChange (reduceMap gS) (baseChange (Ideal.Quotient.mk (pIdeal p S)) (baseChange y₀ (baseChange f₀ (γ 0)))), 0),
            ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb').nVarpi (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb').nMk (baseChange (reduceMap gS) (baseChange (Ideal.Quotient.mk (pIdeal p S)) (baseChange y₀ (baseChange f₀ (γ 1)))), 0))] i) := by
  classical

  let φ : (WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* S' ⧸ pIdeal p S' := (reduceMap gS).comp (reduceMap y₀)
  have hring1 : (φ.comp (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = ((reduceMap gS).comp (Ideal.Quotient.mk (pIdeal p S))).comp y₀ :=
    RingHom.ext fun x => rfl
  have hring2 : (φ.comp (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (residueMap (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) = (reduceMap gS).comp (residueMap (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) :=
    RingHom.ext fun x => by
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
  have hring3 : (φ.comp (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = ((reduceMap gS).comp (reduceMap y₀)).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) := by
    rw [Rigidified.reduceMap_id, RingHom.comp_id]

  have hXφ : ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).XbarS (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).F.map φ = (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).F := by
    show (((X.map f₀).F.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))).map (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))).map φ = (((X.map f₀).F.map y₀).map (Ideal.Quotient.mk (pIdeal p S))).map (reduceMap gS)
    simp only [map_map_ringHom]
    rw [← RingHom.comp_assoc, hring1, RingHom.comp_assoc]
  have hΦφ : (Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).F.map φ = (Rigidified.PhibarS (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS).F := by
    show ((Φ.F.map (residueMap (Ideal.Quotient.mk (pIdeal p (WittVector p k))))).map (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))).map φ = (Φ.F.map (residueMap (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))).map (reduceMap gS)
    simp only [map_map_ringHom]
    rw [← RingHom.comp_assoc, hring2]

  let BCX : CartierModule p ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).XbarS (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).F →+ CartierModule p (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).F := baseChangeEq φ hXφ
  let BCΦ : CartierModule p (Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).F →+
      CartierModule p (Rigidified.PhibarS (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS).F := baseChangeEq φ hΦφ
  have hXV : ∀ x, BCX ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).XbarS (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).verschiebung x) = ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb').verschiebung (BCX x) := fun x =>
    baseChangeEq_verschiebungInt φ hXφ x
  have hXPi : ∀ x, BCX ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).XbarS (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).varpi x) = ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb').varpi (BCX x) := fun x =>
    baseChangeEq_endAct φ hXφ (φ := ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).XbarS (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).varpiEnd) (ψ := (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).varpiEnd) (fun i => by
      show MvPowerSeries.map (reduceMap gS) (MvPowerSeries.map (Ideal.Quotient.mk (pIdeal p S)) (MvPowerSeries.map y₀ (MvPowerSeries.map f₀ (X.varpi i)))) =
        MvPowerSeries.map φ (MvPowerSeries.map (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (MvPowerSeries.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (MvPowerSeries.map f₀ (X.varpi i))))
      rw [MvPowerSeries.map_map, MvPowerSeries.map_map, MvPowerSeries.map_map, MvPowerSeries.map_map,
        MvPowerSeries.map_map, MvPowerSeries.map_map, hring1]) x
  have hΦV : ∀ x, BCΦ (((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg).verschiebung x) = ((Rigidified.PhibarS (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS).toGradedCartierModuleData (Rigidified.jPhiS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcΦg').verschiebung (BCΦ x) := fun x =>
    baseChangeEq_verschiebungInt φ hΦφ x
  have hΦPi : ∀ x, BCΦ (((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg).varpi x) = ((Rigidified.PhibarS (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS).toGradedCartierModuleData (Rigidified.jPhiS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcΦg').varpi (BCΦ x) := fun x =>
    baseChangeEq_endAct φ hΦφ (φ := (Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).varpiEnd)
      (ψ := (Rigidified.PhibarS (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS).varpiEnd) (fun i => by
      show MvPowerSeries.map (reduceMap gS) (MvPowerSeries.map (residueMap (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Φ.varpi i)) =
        MvPowerSeries.map φ (MvPowerSeries.map (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (MvPowerSeries.map (residueMap (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Φ.varpi i)))
      rw [MvPowerSeries.map_map, MvPowerSeries.map_map, MvPowerSeries.map_map, hring2]) x

  have hρV0 := Rigidified.rhoC_verschiebungInt (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀.1 (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
  have hρPi0 := Rigidified.rhoC_endAct_varpiEnd (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
  have hρV1 := Rigidified.rhoC_verschiebungInt (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) hOD'.1 gS
  have hρPi1 := Rigidified.rhoC_endAct_varpiEnd (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) hOD' gS
  have hbV0 := Rigidified.bcPhi_verschiebungInt (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
  have hbPi0 := Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
  have hbV1 := Rigidified.bcPhi_verschiebungInt (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS
  have hbPi1 := Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS

  have hsq1 : ∀ x, ((BCX).comp (Rigidified.rhoC (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀.1 (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))) x =
      ((Rigidified.rhoC (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) hOD'.1 gS).comp BCΦ) x := fun x => by
    show baseChangeEq φ hXφ (CartierModule.map ((hOD₀.1.map (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))).toHom) x) =
      CartierModule.map ((hOD'.1.map (reduceMap gS)).toHom) (baseChangeEq φ hΦφ x)
    exact baseChangeEq_map φ hΦφ hXφ (fun i => by
      show MvPowerSeries.map (reduceMap gS) (MvPowerSeries.map (reduceMap y₀) (MvPowerSeries.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (ρ₀ i))) =
        MvPowerSeries.map φ (MvPowerSeries.map (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (MvPowerSeries.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (ρ₀ i)))
      rw [MvPowerSeries.map_map, MvPowerSeries.map_map, MvPowerSeries.map_map, MvPowerSeries.map_map, hring3]) x
  have hsq2 : ∀ u, ((BCΦ).comp (Rigidified.bcPhi (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))) u =
      (Rigidified.bcPhi (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) u := fun u => by
    refine MvFormalGroup.CartierModule.ext (funext fun jj => ?_)
    show MvPowerSeries.map φ (MvPowerSeries.map (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (MvPowerSeries.map (residueMap (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (u.toPowerSeries jj))) =
      MvPowerSeries.map (reduceMap gS) (MvPowerSeries.map (residueMap (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (u.toPowerSeries jj))
    rw [MvPowerSeries.map_map, MvPowerSeries.map_map, MvPowerSeries.map_map, hring2]

  have hA : ∀ z, ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).XbarS (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMap ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb') BCX hXV hXPi) ((((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg).nMap (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).XbarS (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb) (Rigidified.rhoC (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀.1 (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hρV0 hρPi0) z) = (((Rigidified.PhibarS (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS).toGradedCartierModuleData (Rigidified.jPhiS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcΦg').nMap ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb') (Rigidified.rhoC (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) hOD'.1 gS) hρV1 hρPi1) ((((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg).nMap ((Rigidified.PhibarS (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS).toGradedCartierModuleData (Rigidified.jPhiS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcΦg') BCΦ hΦV hΦPi) z) := fun z => by
    rw [← RhoCompat.nMap_comp_apply ((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg) (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).XbarS (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb) ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb') (Rigidified.rhoC (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀.1 (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hρV0 hρPi0 BCX hXV hXPi
        (RhoCompat.comp_compat (Rigidified.rhoC (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀.1 (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) BCX _ _ _ hρV0 hXV) (RhoCompat.comp_compat (Rigidified.rhoC (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀.1 (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) BCX _ _ _ hρPi0 hXPi) z,
      ← RhoCompat.nMap_comp_apply ((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg) ((Rigidified.PhibarS (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS).toGradedCartierModuleData (Rigidified.jPhiS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcΦg') ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb') BCΦ hΦV hΦPi (Rigidified.rhoC (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) hOD'.1 gS) hρV1 hρPi1
        (RhoCompat.comp_compat BCΦ (Rigidified.rhoC (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) hOD'.1 gS) _ _ _ hΦV hρV1) (RhoCompat.comp_compat BCΦ (Rigidified.rhoC (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) hOD'.1 gS) _ _ _ hΦPi hρPi1) z]
    exact RhoCompat.nMap_congr ((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg) ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb') _ _ hsq1 _ _ _ _ z
  have hB : ∀ u, (((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg).nMap ((Rigidified.PhibarS (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS).toGradedCartierModuleData (Rigidified.jPhiS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcΦg') BCΦ hΦV hΦPi) (((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg) (Rigidified.bcPhi (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hbV0 hbPi0) u) = ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS).toGradedCartierModuleData (Rigidified.jPhiS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcΦg') (Rigidified.bcPhi (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hbV1 hbPi1) u := fun u => by
    rw [← RhoCompat.nMap_comp_apply (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) ((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg) ((Rigidified.PhibarS (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS).toGradedCartierModuleData (Rigidified.jPhiS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcΦg') (Rigidified.bcPhi (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hbV0 hbPi0 BCΦ hΦV hΦPi
        (RhoCompat.comp_compat (Rigidified.bcPhi (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) BCΦ _ _ _ hbV0 hΦV) (RhoCompat.comp_compat (Rigidified.bcPhi (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) BCΦ _ _ _ hbPi0 hΦPi) u]
    exact RhoCompat.nMap_congr (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) ((Rigidified.PhibarS (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS).toGradedCartierModuleData (Rigidified.jPhiS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcΦg') _ _ hsq2 _ _ _ _ u
  have hkey : ∀ w, Rigidified.rigidNum ι hcΦ rΦ (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) hOD' gS hcb' hcΦg' w =
      ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).XbarS (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMap ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb') BCX hXV hXPi) (Rigidified.rigidNum ι hcΦ rΦ (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) hcb hcΦg w) := by
    intro w
    show (((Rigidified.PhibarS (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS).toGradedCartierModuleData (Rigidified.jPhiS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcΦg').nMap ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb') (Rigidified.rhoC (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) hOD'.1 gS) hρV1 hρPi1) (((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS).toGradedCartierModuleData (Rigidified.jPhiS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcΦg') (Rigidified.bcPhi (Φ := Φ) (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hbV1 hbPi1) (rΦ w)) = ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).XbarS (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMap ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb') BCX hXV hXPi) ((((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg).nMap (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).XbarS (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb) (Rigidified.rhoC (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀.1 (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hρV0 hρPi0) (((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg) (Rigidified.bcPhi (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hbV0 hbPi0) (rΦ w)))
    rw [hA, hB]

  have hvec : ∀ j : Fin 2, BCX (baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ j)))) =
      baseChange (reduceMap gS) (baseChange (Ideal.Quotient.mk (pIdeal p S)) (baseChange y₀ (baseChange f₀ (γ j)))) := by
    intro j
    refine MvFormalGroup.CartierModule.ext (funext fun jj => ?_)
    show MvPowerSeries.map φ (MvPowerSeries.map (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (MvPowerSeries.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (MvPowerSeries.map f₀ ((γ j).toPowerSeries jj)))) =
      MvPowerSeries.map (reduceMap gS) (MvPowerSeries.map (Ideal.Quotient.mk (pIdeal p S)) (MvPowerSeries.map y₀ (MvPowerSeries.map f₀ ((γ j).toPowerSeries jj))))
    rw [MvPowerSeries.map_map, MvPowerSeries.map_map, MvPowerSeries.map_map, MvPowerSeries.map_map,
      MvPowerSeries.map_map, MvPowerSeries.map_map, hring1]
  have hN0 : ∀ x, (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).XbarS (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMap ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb') BCX hXV hXPi ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).XbarS (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk (x, 0)) = ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb').nMk (BCX x, 0) := fun x => by
    rw [nMap_nMk, map_zero]
    try rfl

  intro i
  have key := congrArg ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).XbarS (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMap ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb') BCX hXV hXPi) (hN i)
  rw [map_nsmul, map_nsmul, ← hkey, RhoCompat.vec2_map ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).XbarS (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMap ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb') BCX hXV hXPi),
    RhoCompat.nMap_nVarpi, hN0, hN0, hvec, hvec] at key
  exact key

end S_CerednikDrinfeld_FormalODModule_smul_rigidNum_map_node_single_eq_smul_baseChange_of_rigidNum_single_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_smul_rigidNum_map_node_single_eq_smul_baseChange_of_rigidNum_single_eq (solution)
