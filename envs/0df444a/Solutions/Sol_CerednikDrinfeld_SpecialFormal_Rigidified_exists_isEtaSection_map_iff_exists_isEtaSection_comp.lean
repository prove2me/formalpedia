-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_iff_exists_isEtaSection_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/982dba69-e735-5731-b8ba-9caf9df58b06

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

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_iff_exists_isEtaSection_comp

set_option autoImplicit false

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_iff_exists_isEtaSection_comp.CerednikDrinfeld CerednikDrinfeld.SpecialFormal P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_iff_exists_isEtaSection_comp.CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega"

open scoped PadicInt Padic

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule FormalODModule.map_map FormalODModule.IsODHom SpecialFormal.Rigidified GradedCartierModuleData"
namespace SpecialFormal
p2m_export "CerednikDrinfeld.SpecialFormal" "Series Series.map_map pIdeal residueMap reduceMap Rigidified residueMap_comp Rigidified.map_comp Rigidified.jbar Rigidified.IsGradedPhiS"
namespace Rigidified
p2m_export "CerednikDrinfeld.SpecialFormal.Rigidified" "Xbar Φbar map map_ρ reduceMap_comp map_comp mk n ρ X jbar XS XbarS PhibarS redC bcPhi rhoC redC_verschiebungInt redC_endAct_varpiEnd bcPhi_verschiebungInt bcPhi_endAct_varpiEnd rhoC_verschiebungInt rhoC_endAct_varpiEnd jS jSbar jPhiS IsGradedS IsGradedSbar IsGradedPhiS etaRed rigidNum LatticeRel IsEtaSection"
p2m_open "CerednikDrinfeld.SpecialFormal.Rigidified CerednikDrinfeld.SpecialFormal CerednikDrinfeld"

p2m_open "CerednikDrinfeld.FormalODModule CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData"

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

namespace Reindex

def GenEta (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    {S : Type} [CommRing S]
    (jS : Zp2 p →+* S) (jSb jPhi : Zp2 p →+* S ⧸ pIdeal p S)
    (X : FormalODModule p S) (Xb Φb : FormalODModule p (S ⧸ pIdeal p S))
    (red : CartierModule p X.F →+ CartierModule p Xb.F)
    (hredV : ∀ m, red (verschiebungInt m) = verschiebungInt (red m))
    (hredϖ : ∀ m, red (endAct X.varpiEnd m) = endAct Xb.varpiEnd (red m))
    (ρC : CartierModule p Φb.F →+ CartierModule p Xb.F)
    (hρV : ∀ m, ρC (verschiebungInt m) = verschiebungInt (ρC m))
    (hρϖ : ∀ m, ρC (endAct Φb.varpiEnd m) = endAct Xb.varpiEnd (ρC m))
    (β : CartierModule p Φ.F →+ CartierModule p Φb.F)
    (hβV : ∀ m, β (verschiebungInt m) = verschiebungInt (β m))
    (hβϖ : ∀ m, β (endAct Φ.varpiEnd m) = endAct Φb.varpiEnd (β m))
    (n : ℕ)
    (hc : IsCompl (X.gradedPiece jS 0) (X.gradedPiece jS 1))
    (hcb : IsCompl (Xb.gradedPiece jSb 0) (Xb.gradedPiece jSb 1))
    (hcΦg : IsCompl (Φb.gradedPiece jPhi 0) (Φb.gradedPiece jPhi 1))
    (L : (X.toGradedCartierModuleData jS hc).M →+ (X.toGradedCartierModuleData jS hc).NMod)
    (hL : (X.toGradedCartierModuleData jS hc).IsCanonicalLMap L)
    (i : Fin 2) (z : (X.toGradedCartierModuleData jS hc).NMod) (v : Fin 2 → ℚ_[p]) : Prop :=
  let D := X.toGradedCartierModuleData jS hc
  z ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung i ∧
    LatticeRel (Xb.toGradedCartierModuleData jSb hcb) n
      (((Φb.toGradedCartierModuleData jPhi hcΦg).nMap (Xb.toGradedCartierModuleData jSb hcb) ρC hρV hρϖ).comp
        (((Φ.toGradedCartierModuleData (jbar ι) hcΦ).nMap (Φb.toGradedCartierModuleData jPhi hcΦg) β hβV hβϖ).comp
          rΦ))
      ((X.toGradedCartierModuleData jS hc).nMap (Xb.toGradedCartierModuleData jSb hcb) red hredV hredϖ
        (((D.nVarpi : D.NMod →ₗ[WittVector p S] D.NMod) ^ (i : ℕ)) z))
      ((p : ℚ_[p]) ^ (i : ℕ) • v)

def GenEx (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    {S : Type} [CommRing S]
    (jS : Zp2 p →+* S) (jSb jPhi : Zp2 p →+* S ⧸ pIdeal p S)
    (X : FormalODModule p S) (Xb Φb : FormalODModule p (S ⧸ pIdeal p S))
    (red : CartierModule p X.F →+ CartierModule p Xb.F)
    (hredV : ∀ m, red (verschiebungInt m) = verschiebungInt (red m))
    (hredϖ : ∀ m, red (endAct X.varpiEnd m) = endAct Xb.varpiEnd (red m))
    (ρC : CartierModule p Φb.F →+ CartierModule p Xb.F)
    (hρV : ∀ m, ρC (verschiebungInt m) = verschiebungInt (ρC m))
    (hρϖ : ∀ m, ρC (endAct Φb.varpiEnd m) = endAct Xb.varpiEnd (ρC m))
    (β : CartierModule p Φ.F →+ CartierModule p Φb.F)
    (hβV : ∀ m, β (verschiebungInt m) = verschiebungInt (β m))
    (hβϖ : ∀ m, β (endAct Φ.varpiEnd m) = endAct Φb.varpiEnd (β m))
    (n : ℕ) (i : Fin 2) (v : Fin 2 → ℚ_[p]) : Prop :=
  ∃ (hc : IsCompl (X.gradedPiece jS 0) (X.gradedPiece jS 1))
    (hcb : IsCompl (Xb.gradedPiece jSb 0) (Xb.gradedPiece jSb 1))
    (hcΦg : IsCompl (Φb.gradedPiece jPhi 0) (Φb.gradedPiece jPhi 1))
    (L : _) (hL : (X.toGradedCartierModuleData jS hc).IsCanonicalLMap L),
    ∃ z, GenEta ι hcΦ rΦ jS jSb jPhi X Xb Φb red hredV hredϖ ρC hρV hρϖ β hβV hβϖ n hc hcb hcΦg L hL i z v

theorem genEx_congr (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    {S : Type} [CommRing S]
    {jS₁ jS₂ : Zp2 p →+* S} {jSb₁ jSb₂ jPhi₁ jPhi₂ : Zp2 p →+* S ⧸ pIdeal p S}
    {X₁ X₂ : FormalODModule p S} {Xb₁ Xb₂ Φb₁ Φb₂ : FormalODModule p (S ⧸ pIdeal p S)}
    {red₁ : CartierModule p X₁.F →+ CartierModule p Xb₁.F} {red₂ : CartierModule p X₂.F →+ CartierModule p Xb₂.F}
    (hredV₁ : ∀ m, red₁ (verschiebungInt m) = verschiebungInt (red₁ m))
    (hredϖ₁ : ∀ m, red₁ (endAct X₁.varpiEnd m) = endAct Xb₁.varpiEnd (red₁ m))
    (hredV₂ : ∀ m, red₂ (verschiebungInt m) = verschiebungInt (red₂ m))
    (hredϖ₂ : ∀ m, red₂ (endAct X₂.varpiEnd m) = endAct Xb₂.varpiEnd (red₂ m))
    {ρC₁ : CartierModule p Φb₁.F →+ CartierModule p Xb₁.F} {ρC₂ : CartierModule p Φb₂.F →+ CartierModule p Xb₂.F}
    (hρV₁ : ∀ m, ρC₁ (verschiebungInt m) = verschiebungInt (ρC₁ m))
    (hρϖ₁ : ∀ m, ρC₁ (endAct Φb₁.varpiEnd m) = endAct Xb₁.varpiEnd (ρC₁ m))
    (hρV₂ : ∀ m, ρC₂ (verschiebungInt m) = verschiebungInt (ρC₂ m))
    (hρϖ₂ : ∀ m, ρC₂ (endAct Φb₂.varpiEnd m) = endAct Xb₂.varpiEnd (ρC₂ m))
    {β₁ : CartierModule p Φ.F →+ CartierModule p Φb₁.F} {β₂ : CartierModule p Φ.F →+ CartierModule p Φb₂.F}
    (hβV₁ : ∀ m, β₁ (verschiebungInt m) = verschiebungInt (β₁ m))
    (hβϖ₁ : ∀ m, β₁ (endAct Φ.varpiEnd m) = endAct Φb₁.varpiEnd (β₁ m))
    (hβV₂ : ∀ m, β₂ (verschiebungInt m) = verschiebungInt (β₂ m))
    (hβϖ₂ : ∀ m, β₂ (endAct Φ.varpiEnd m) = endAct Φb₂.varpiEnd (β₂ m))
    {n₁ n₂ : ℕ} (i : Fin 2) (v : Fin 2 → ℚ_[p])
    (ejS : jS₁ = jS₂) (ejSb : jSb₁ = jSb₂) (ejPhi : jPhi₁ = jPhi₂)
    (eX : X₁ = X₂) (eXb : Xb₁ = Xb₂) (eΦb : Φb₁ = Φb₂)
    (ered : HEq red₁ red₂) (eρ : HEq ρC₁ ρC₂) (eβ : HEq β₁ β₂) (en : n₁ = n₂) :
    GenEx ι hcΦ rΦ jS₁ jSb₁ jPhi₁ X₁ Xb₁ Φb₁ red₁ hredV₁ hredϖ₁ ρC₁ hρV₁ hρϖ₁ β₁ hβV₁ hβϖ₁ n₁ i v ↔
      GenEx ι hcΦ rΦ jS₂ jSb₂ jPhi₂ X₂ Xb₂ Φb₂ red₂ hredV₂ hredϖ₂ ρC₂ hρV₂ hρϖ₂ β₂ hβV₂ hβϖ₂ n₂ i v := by
  subst ejS ejSb ejPhi eX eXb eΦb en
  cases ered
  cases eρ
  cases eβ
  exact Iff.rfl

theorem heq_baseChangeEq {R S : Type} [CommRing R] [CommRing S] {X₁ X₂ : FormalODModule p R} {Y₁ Y₂ : FormalODModule p S}
    (f₁ f₂ : R →+* S) (h₁ : X₁.F.map f₁ = Y₁.F) (h₂ : X₂.F.map f₂ = Y₂.F) (eX : X₁ = X₂) (eY : Y₁ = Y₂)
    (ef : f₁ = f₂) :
    HEq (baseChangeEq (p := p) (Φ := X₁.F) (Ψ := Y₁.F) f₁ h₁) (baseChangeEq (p := p) (Φ := X₂.F) (Ψ := Y₂.F) f₂ h₂) := by
  subst eX eY ef
  rfl

theorem heq_cartierMap {S : Type} [CommRing S] {P₁ P₂ Q₁ Q₂ : FormalODModule p S}
    (φ₁ : MvFormalGroup.Hom P₁.F Q₁.F) (φ₂ : MvFormalGroup.Hom P₂.F Q₂.F)
    (eP : P₁ = P₂) (eQ : Q₁ = Q₂) (e : φ₁.toPowerSeries = φ₂.toPowerSeries) :
    HEq (CartierModule.map (p := p) φ₁) (CartierModule.map (p := p) φ₂) := by
  subst eP eQ
  obtain rfl : φ₁ = φ₂ := MvFormalGroup.Hom.ext e
  rfl

end Reindex

open Reindex in

theorem bcPhi_eq_baseChangeEq {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B] {S : Type} [CommRing S]
    (ψ : O →+* B) (g : B →+* S) :
    bcPhi (Φ := Φ) ψ g = baseChangeEq (Φ := Φ.F) (Ψ := (PhibarS (Φ := Φ) ψ g).F) ((reduceMap g).comp (residueMap ψ))
      (MvFormalGroup.map_map' (residueMap ψ) (reduceMap g) Φ.F).symm := by
  apply AddMonoidHom.ext
  intro m
  exact baseChangeEq_baseChangeEq (residueMap ψ) (reduceMap g) rfl rfl _ m

open Reindex in

theorem isEtaSection_iff_genEta (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] (ψ : O →+* B) (t : Rigidified p Φ B) (hOD : IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    {S : Type} [CommRing S] (g : B →+* S)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).M →+ ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).IsCanonicalLMap L)
    (i : Fin 2) (z : ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).NMod) (v : Fin 2 → ℚ_[p]) :
    t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i z v ↔
      GenEta ι hcΦ rΦ (jS ι ψ g) (jSbar ι ψ g) (jPhiS ι ψ g) (t.XS g) (t.XbarS g) (PhibarS (Φ := Φ) ψ g)
        (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g)
        (rhoC ψ t hOD.1 g) (rhoC_verschiebungInt ψ t hOD.1 g) (rhoC_endAct_varpiEnd ψ t hOD g)
        (bcPhi (Φ := Φ) ψ g) (bcPhi_verschiebungInt (Φ := Φ) ψ g) (bcPhi_endAct_varpiEnd (Φ := Φ) ψ g)
        t.n hc hcb hcΦg L hL i z v :=
  Iff.rfl

end CerednikDrinfeld.SpecialFormal.Rigidified

open _root_.CerednikDrinfeld.SpecialFormal.Rigidified _root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_iff_exists_isEtaSection_comp.CerednikDrinfeld.SpecialFormal.Rigidified CerednikDrinfeld.SpecialFormal.Rigidified.Reindex CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData in

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    {B' : Type} [CommRing B'] (g₀ : B →+* B')
    (hOD' : FormalODModule.IsODHom ((t.map g₀).Φbar (g₀.comp ψ)) (t.map g₀).Xbar (t.map g₀).ρ)
    {S : Type} [CommRing S] (h : B' →+* S) (i : Fin 2) (v : Fin 2 → ℚ_[p]) :
    (∃ (hc : (t.map g₀).IsGradedS ι (g₀.comp ψ) h) (hcb : (t.map g₀).IsGradedSbar ι (g₀.comp ψ) h)
        (hcΦh : Rigidified.IsGradedPhiS (Φ := Φ) ι (g₀.comp ψ) h)
        (L : _) (hL : (((t.map g₀).XS h).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
        ∃ z, (t.map g₀).IsEtaSection ι hcΦ rΦ (g₀.comp ψ) hOD' h hc hcb hcΦh L hL i z v) ↔
    (∃ (hc : t.IsGradedS ι ψ (h.comp g₀)) (hcb : t.IsGradedSbar ι ψ (h.comp g₀))
        (hcΦh : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (h.comp g₀))
        (L : _) (hL : ((t.XS (h.comp g₀)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
        ∃ z, t.IsEtaSection ι hcΦ rΦ ψ hOD (h.comp g₀) hc hcb hcΦh L hL i z v) := by

  have eX : (t.map g₀).XS h = t.XS (h.comp g₀) := FormalODModule.map_map g₀ h t.X
  have eXb : (t.map g₀).XbarS h = t.XbarS (h.comp g₀) := by
    show ((t.X.map g₀).map (Ideal.Quotient.mk (pIdeal p B'))).map (reduceMap h) =
      (t.X.map (Ideal.Quotient.mk (pIdeal p B))).map (reduceMap (h.comp g₀))
    simp only [FormalODModule.map_map]
    congr 1
  have eΦb : PhibarS (Φ := Φ) (g₀.comp ψ) h = PhibarS (Φ := Φ) ψ (h.comp g₀) := by
    show (Φ.map (residueMap (g₀.comp ψ))).map (reduceMap h) = (Φ.map (residueMap ψ)).map (reduceMap (h.comp g₀))
    rw [FormalODModule.map_map, FormalODModule.map_map, residueMap_comp, reduceMap_comp, RingHom.comp_assoc]
  have ef : (reduceMap h).comp (residueMap (p := p) (g₀.comp ψ)) = (reduceMap (h.comp g₀)).comp (residueMap ψ) := by
    rw [residueMap_comp, reduceMap_comp, RingHom.comp_assoc]
  have ejS : jS ι (g₀.comp ψ) h = jS ι ψ (h.comp g₀) := RingHom.ext fun _ => rfl
  have ejSb : jSbar ι (g₀.comp ψ) h = jSbar ι ψ (h.comp g₀) := RingHom.ext fun _ => rfl
  have ejPhi : jPhiS ι (g₀.comp ψ) h = jPhiS ι ψ (h.comp g₀) := RingHom.ext fun _ => rfl
  have ered : HEq ((t.map g₀).redC h) (t.redC (h.comp g₀)) :=
    heq_baseChangeEq _ _ _ _ eX eXb rfl
  have eρ : HEq (rhoC (g₀.comp ψ) (t.map g₀) hOD'.1 h) (rhoC ψ t hOD.1 (h.comp g₀)) := by
    refine heq_cartierMap _ _ eΦb eXb ?_
    show ((t.map g₀).ρ).map (reduceMap h) = t.ρ.map (reduceMap (h.comp g₀))
    rw [map_ρ, Series.map_map, ← reduceMap_comp]
  have eβ : HEq (bcPhi (Φ := Φ) (g₀.comp ψ) h) (bcPhi (Φ := Φ) ψ (h.comp g₀)) := by
    rw [bcPhi_eq_baseChangeEq, bcPhi_eq_baseChangeEq]
    exact heq_baseChangeEq _ _ _ _ rfl eΦb ef
  exact genEx_congr ι hcΦ rΦ _ _ _ _ _ _ _ _ _ _ _ _ i v ejS ejSb ejPhi eX eXb eΦb ered eρ eβ rfl

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_iff_exists_isEtaSection_comp
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_iff_exists_isEtaSection_comp (solution)
