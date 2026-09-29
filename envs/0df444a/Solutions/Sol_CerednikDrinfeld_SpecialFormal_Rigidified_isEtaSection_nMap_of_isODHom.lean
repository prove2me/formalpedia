-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_nMap_of_isODHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/18b22569-1463-5aea-b744-c821d6918a36

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_nMap_of_isODHom

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

namespace IsoTrEta

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

section Abstract

variable {p : ℕ} [Fact p.Prime]

theorem nVarpi_nMk {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (m m' : D.M) : D.nVarpi (D.nMk (m, m')) = D.nMk (D.varpi m, D.varpi m') := rfl

theorem nsmul_nMk {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (k : ℕ) (m m' : D.M) : k • D.nMk (m, m') = D.nMk (k • m, k • m') := by
  rw [← map_nsmul]; rfl

theorem nMap_nVarpi {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (z : D.NMod) :
    D.nMap D' f hV hPi (D.nVarpi z) = D'.nVarpi (D.nMap D' f hV hPi z) := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [nVarpi_nMk, nMap_nMk, nMap_nMk, nVarpi_nMk, hPi, hPi]

theorem nMap_nVarpi_pow {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B}
    {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (n : ℕ) (z : D.NMod) :
    D.nMap D' f hV hPi (((D.nVarpi : D.NMod →ₗ[WittVector p B] D.NMod) ^ n) z) =
      ((D'.nVarpi : D'.NMod →ₗ[WittVector p B'] D'.NMod) ^ n) (D.nMap D' f hV hPi z) := by
  induction n generalizing z with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, nMap_nVarpi]

theorem nMap_mem_etaPiece {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D D' : GradedCartierModuleData p B j) (f : D.M →+ D'.M)
    (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (hpc : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i)
    (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (L' : D'.M →+ D'.NMod) (hL' : ∀ x : D'.M, L' (D'.verschiebung x) = D'.nMk (D'.varpi x, 0))
    (hLL' : ∀ x, L' (f x) = D.nMap D' f hV hPi (L x))
    (i : Fin 2) (z : D.NMod) (hz : z ∈ D.etaPiece L hL i) :
    D.nMap D' f hV hPi z ∈ D'.etaPiece L' hL' i := by
  obtain ⟨hfix, hpiece⟩ := AddSubgroup.mem_inf.mp hz
  refine AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_eta_iff] at hfix ⊢
    obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective z
    calc D'.phi L' hL' (D.nMap D' f hV hPi (D.nMk (x, x')))
        = D.nMap D' f hV hPi (L x) + D'.nMk (f x', 0) := by rw [nMap_nMk, phi_nMk, hLL']
      _ = D.nMap D' f hV hPi (L x + D.nMk (x', 0)) := by rw [map_add, nMap_nMk, map_zero]
      _ = D.nMap D' f hV hPi (D.phi L hL (D.nMk (x, x'))) := by rw [phi_nMk]
      _ = D.nMap D' f hV hPi (D.nMk (x, x')) := by rw [hfix]
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := AddSubgroup.mem_map.mp hpiece
    obtain ⟨ha, hb⟩ := AddSubgroup.mem_prod.mp hab
    rw [nMap_nMk]
    exact AddSubgroup.mem_map.mpr ⟨(f a, f b), AddSubgroup.mem_prod.mpr ⟨hpc i a ha, hpc i b hb⟩, rfl⟩

theorem nMap_nMap_comm {B1 B2 B3 B4 : Type} [CommRing B1] [CommRing B2] [CommRing B3] [CommRing B4]
    {j1 : Zp2 p →+* B1} {j2 : Zp2 p →+* B2} {j3 : Zp2 p →+* B3} {j4 : Zp2 p →+* B4}
    (D1 : GradedCartierModuleData p B1 j1) (D2 : GradedCartierModuleData p B2 j2)
    (D3 : GradedCartierModuleData p B3 j3) (D4 : GradedCartierModuleData p B4 j4)
    (f : D1.M →+ D2.M) (hfV : ∀ x, f (D1.verschiebung x) = D2.verschiebung (f x))
    (hfPi : ∀ x, f (D1.varpi x) = D2.varpi (f x))
    (g : D2.M →+ D4.M) (hgV : ∀ x, g (D2.verschiebung x) = D4.verschiebung (g x))
    (hgPi : ∀ x, g (D2.varpi x) = D4.varpi (g x))
    (h : D1.M →+ D3.M) (hhV : ∀ x, h (D1.verschiebung x) = D3.verschiebung (h x))
    (hhPi : ∀ x, h (D1.varpi x) = D3.varpi (h x))
    (k : D3.M →+ D4.M) (hkV : ∀ x, k (D3.verschiebung x) = D4.verschiebung (k x))
    (hkPi : ∀ x, k (D3.varpi x) = D4.varpi (k x))
    (hc : ∀ x, g (f x) = k (h x)) (z : D1.NMod) :
    D2.nMap D4 g hgV hgPi (D1.nMap D2 f hfV hfPi z) =
      D3.nMap D4 k hkV hkPi (D1.nMap D3 h hhV hhPi z) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D1.nMk_surjective z
  rw [nMap_nMk, nMap_nMk, nMap_nMk, nMap_nMk, hc, hc]

theorem nsmul_nMap_nMap_eq {B1 B2 B3 : Type} [CommRing B1] [CommRing B2] [CommRing B3]
    {j1 : Zp2 p →+* B1} {j2 : Zp2 p →+* B2} {j3 : Zp2 p →+* B3}
    (D1 : GradedCartierModuleData p B1 j1) (D2 : GradedCartierModuleData p B2 j2)
    (D3 : GradedCartierModuleData p B3 j3)
    (ρ : D1.M →+ D2.M) (hρV : ∀ x, ρ (D1.verschiebung x) = D2.verschiebung (ρ x))
    (hρPi : ∀ x, ρ (D1.varpi x) = D2.varpi (ρ x))
    (u : D2.M →+ D3.M) (huV : ∀ x, u (D2.verschiebung x) = D3.verschiebung (u x))
    (huPi : ∀ x, u (D2.varpi x) = D3.varpi (u x))
    (ρ' : D1.M →+ D3.M) (hρ'V : ∀ x, ρ' (D1.verschiebung x) = D3.verschiebung (ρ' x))
    (hρ'Pi : ∀ x, ρ' (D1.varpi x) = D3.varpi (ρ' x))
    (e₁ e₂ : ℕ) (he : ∀ a, e₁ • u (ρ a) = e₂ • ρ' a) (y : D1.NMod) :
    e₁ • D2.nMap D3 u huV huPi (D1.nMap D2 ρ hρV hρPi y) = e₂ • D1.nMap D3 ρ' hρ'V hρ'Pi y := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D1.nMk_surjective y
  rw [nMap_nMk, nMap_nMk, nMap_nMk, nsmul_nMk, nsmul_nMk, he, he]

theorem lattice_transport {M1 M2 M3 : Type*} [AddCommMonoid M1] [AddCommMonoid M2]
    [AddCommMonoid M3] (Nρ : M1 →+ M2) (Nρ' : M1 →+ M3) (Nu : M2 →+ M3)
    (q e₁ e₂ n m k : ℕ) (hK : ∀ y, q ^ e₁ • Nu (Nρ y) = q ^ e₂ • Nρ' y) (y : M1) (R : M2)
    (hrel : q ^ k • Nρ y = q ^ (k + n + m) • R) :
    q ^ (k + e₂) • Nρ' y = q ^ (e₁ + (k + n + m)) • Nu R := by
  rw [pow_add, pow_add q e₁, mul_smul, mul_smul, ← hK, smul_comm (q ^ k) (q ^ e₁) (Nu (Nρ y)),
    ← map_nsmul Nu (q ^ k) (Nρ y), hrel, map_nsmul]

end Abstract

section Cartier

variable {p : ℕ} [Fact p.Prime]

open MvFormalGroup MvFormalGroup.CartierModule

theorem nsmul_map_eq_map_comp {R : Type} [CommRing R] {d : ℕ} {Φ Φ' : MvFormalGroup d R}
    [Φ.IsComm] [Φ'.IsComm] (h : Φ.Hom Φ') (e : ℕ) (m : CartierModule p Φ) :
    e • CartierModule.map h m = CartierModule.map ((e : MvFormalGroup.End Φ').comp h) m := by
  rw [map_comp, ← endAct_natCast, endAct_apply]

end Cartier

end IsoTrEta

theorem solution
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] (ψ : O →+* B)
    (t t' : Rigidified p Φ B)
    (us ws : Series B) (hu : FormalODModule.IsODHom t.X t'.X us) (hw : FormalODModule.IsODHom t'.X t.X ws)
    (hwu : ws.comp us = Series.id B) (huw : us.comp ws = Series.id B)
    (m₀ : ℕ)
    (hρ : (t'.Xbar.act ((p : Zp2 p) ^ (m₀ + t'.n))).comp
        ((us.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ) =
      (t'.Xbar.act ((p : Zp2 p) ^ (m₀ + t.n))).comp t'.ρ)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (hOD' : FormalODModule.IsODHom (t'.Φbar ψ) t'.Xbar t'.ρ)
    {S : Type} [CommRing S] (g : B →+* S)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g)
    (hc' : t'.IsGradedS ι ψ g) (hcb' : t'.IsGradedSbar ι ψ g)
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (fu : CartierModule p (t.XS g).F →+ CartierModule p (t'.XS g).F)
    (hfu : fu = CartierModule.map ((hu.1.map g).toHom : MvFormalGroup.Hom (t.XS g).F (t'.XS g).F))
    (hfuV : ∀ x, fu (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).verschiebung x) =
      ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').verschiebung (fu x))
    (hfuPi : ∀ x, fu (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).varpi x) =
      ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').varpi (fu x))
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M →+
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L)
    (L' : ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').M →+
      ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').NMod)
    (hL' : ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').IsCanonicalLMap L')
    (hLL' : ∀ x, L' (fu x) =
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap
        ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc') fu hfuV hfuPi (L x))
    (i : Fin 2) (z : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod) (v : Fin 2 → ℚ_[p])
    (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i z v) :
    t'.IsEtaSection ι hcΦ rΦ ψ hOD' g hc' hcb' hcΦg L' hL' i
      (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap
        ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc') fu hfuV hfuPi z) v := by

  have huS : FormalODModule.IsODHom (t.XS g) (t'.XS g) (us.map g) := hu.map g
  have hū : FormalODModule.IsODHom (t.XbarS g) (t'.XbarS g)
      ((us.map (Ideal.Quotient.mk (pIdeal p B))).map (reduceMap g)) :=
    (hu.map (Ideal.Quotient.mk (pIdeal p B))).map (reduceMap g)

  have hūV : ∀ x : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).M, CartierModule.map hū.1.toHom (((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).verschiebung x) =
      ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb').verschiebung (CartierModule.map hū.1.toHom x) := fun x => map_verschiebungInt _ x
  have hūPi : ∀ x : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).M, CartierModule.map hū.1.toHom (((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).varpi x) =
      ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb').varpi (CartierModule.map hū.1.toHom x) := by
    intro x
    show CartierModule.map hū.1.toHom (CartierModule.map (t.XbarS g).varpiEnd x) =
      CartierModule.map (t'.XbarS g).varpiEnd (CartierModule.map hū.1.toHom x)
    rw [← map_comp, ← map_comp]
    congr 2
    apply MvFormalGroup.Hom.ext
    exact hū.2.2

  have hpc : ∀ (i : Fin 2) (x : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M), x ∈ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).piece i →
      fu x ∈ ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').piece i := by
    intro i x hx
    rw [hfu]
    have hx' := (FormalODModule.mem_toGradedCartierModuleData_piece_iff (t.XS g)
      (Rigidified.jS ι ψ g) hc i x).mp hx
    refine (FormalODModule.mem_toGradedCartierModuleData_piece_iff (t'.XS g)
      (Rigidified.jS ι ψ g) hc' i _).mpr ?_
    rw [FormalODModule.mem_gradedPiece_iff] at hx' ⊢
    intro c
    have hcomm : ((t'.XS g).actEnd (WittVector.teichmuller p c)).comp
          ((hu.1.map g).toHom : MvFormalGroup.Hom (t.XS g).F (t'.XS g).F) =
        ((hu.1.map g).toHom : MvFormalGroup.Hom (t.XS g).F (t'.XS g).F).comp
          ((t.XS g).actEnd (WittVector.teichmuller p c)) :=
      (MvFormalGroup.Hom.ext (huS.2.1 (WittVector.teichmuller p c))).symm
    erw [endAct_apply, ← map_comp, hcomm, map_comp, ← endAct_apply, hx' c, map_homothety]
    rfl

  have hq : (reduceMap (p := p) g).comp (Ideal.Quotient.mk (pIdeal p B)) =
      (Ideal.Quotient.mk (pIdeal p S)).comp g := RingHom.ext fun _ => rfl
  have hred : ∀ x : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M, t'.redC g (fu x) =
      CartierModule.map hū.1.toHom (t.redC g x) := by
    intro x
    rw [hfu]
    refine baseChangeEq_map (Ideal.Quotient.mk (pIdeal p S)) (t.XS_F_map_mk g) (t'.XS_F_map_mk g)
      (fun i => ?_) x
    show MvPowerSeries.map (reduceMap g) (MvPowerSeries.map (Ideal.Quotient.mk (pIdeal p B)) (us i)) =
      MvPowerSeries.map (Ideal.Quotient.mk (pIdeal p S)) (MvPowerSeries.map g (us i))
    rw [MvPowerSeries.map_map, MvPowerSeries.map_map, hq]

  have hρ0 : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0 := hOD.1.1
  have hρ0' : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0 := hOD'.1.1
  have hu0 : ∀ i, MvPowerSeries.constantCoeff ((us.map (Ideal.Quotient.mk (pIdeal p B))) i) = 0 :=
    (hu.map (Ideal.Quotient.mk (pIdeal p B))).constantCoeff
  have hact : ∀ e : ℕ, (t'.Xbar.act ((p : Zp2 p) ^ e)).map (reduceMap g) =
      MvFormalGroup.Hom.toPowerSeries ((p ^ e : ℕ) : MvFormalGroup.End (t'.XbarS g).F) := by
    intro e
    rw [MvFormalGroup.End.toPowerSeries_natCast, ← FormalODModule.act_natCast, Nat.cast_pow]
    rfl
  have hC2 : ∀ a : CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ g).F,
      p ^ (m₀ + t'.n) • CartierModule.map hū.1.toHom (Rigidified.rhoC ψ t hOD.1 g a) =
        p ^ (m₀ + t.n) • Rigidified.rhoC ψ t' hOD'.1 g a := by
    intro a
    show p ^ (m₀ + t'.n) • CartierModule.map hū.1.toHom
        (CartierModule.map ((hOD.1.map (reduceMap g)).toHom :
          MvFormalGroup.Hom (Rigidified.PhibarS (Φ := Φ) ψ g).F (t.XbarS g).F) a) =
      p ^ (m₀ + t.n) • CartierModule.map ((hOD'.1.map (reduceMap g)).toHom :
          MvFormalGroup.Hom (Rigidified.PhibarS (Φ := Φ) ψ g).F (t'.XbarS g).F) a
    erw [← map_comp, IsoTrEta.nsmul_map_eq_map_comp, IsoTrEta.nsmul_map_eq_map_comp]
    congr 2
    apply MvFormalGroup.Hom.ext
    have key := congrArg (Series.map (reduceMap g)) hρ
    rw [Series.map_comp _ _ _ (Series.constantCoeff_comp hu0 hρ0), Series.map_comp _ _ _ hρ0,
      Series.map_comp _ _ _ hρ0', hact, hact] at key
    exact key

  unfold Rigidified.IsEtaSection at hz ⊢
  obtain ⟨hzeta, m, k, w, hw, hrel⟩ := hz
  refine ⟨IsoTrEta.nMap_mem_etaPiece ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc') _ hfuV hfuPi hpc L _ L' _ hLL' i z hzeta,
    m, k + m₀ + t.n, w, hw, ?_⟩
  rw [← IsoTrEta.nMap_nVarpi_pow]
  simp only [Rigidified.etaRed, Rigidified.rigidNum, AddMonoidHom.coe_comp, Function.comp_apply]
    at hrel ⊢
  rw [IsoTrEta.nMap_nMap_comm ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc') ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb')
    fu hfuV hfuPi
    (t'.redC g) (t'.redC_verschiebungInt g) (t'.redC_endAct_varpiEnd g)
    (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g)
    (CartierModule.map hū.1.toHom) hūV hūPi hred]
  have hK := IsoTrEta.nsmul_nMap_nMap_eq ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg) ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb')
    (Rigidified.rhoC ψ t hOD.1 g) (Rigidified.rhoC_verschiebungInt ψ t hOD.1 g)
    (Rigidified.rhoC_endAct_varpiEnd ψ t hOD g)
    (CartierModule.map hū.1.toHom) hūV hūPi
    (Rigidified.rhoC ψ t' hOD'.1 g) (Rigidified.rhoC_verschiebungInt ψ t' hOD'.1 g)
    (Rigidified.rhoC_endAct_varpiEnd ψ t' hOD' g)
    (p ^ (m₀ + t'.n)) (p ^ (m₀ + t.n)) hC2
  have e1 : k + m₀ + t.n = k + (m₀ + t.n) := by ring
  have e2 : k + m₀ + t.n + t'.n + m = (m₀ + t'.n) + (k + t.n + m) := by ring
  rw [e2, e1]
  exact IsoTrEta.lattice_transport _ _ _ p (m₀ + t'.n) (m₀ + t.n) t.n m k hK _ _ hrel

end S_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_nMap_of_isODHom
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_nMap_of_isODHom (solution)
