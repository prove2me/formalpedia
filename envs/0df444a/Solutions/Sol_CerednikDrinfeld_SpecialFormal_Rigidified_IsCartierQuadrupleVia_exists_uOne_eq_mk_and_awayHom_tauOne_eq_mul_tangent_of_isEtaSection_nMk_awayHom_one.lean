-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_uOne_eq_mk_and_awayHom_tauOne_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/f8a3be4a-7e76-5d8c-9cad-a0e167c70bc3

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
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebung_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_uOne_eq_mk_and_awayHom_tauOne_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

noncomputable section

namespace K3cKit

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.FormalODModule

variable {p : ℕ} [Fact p.Prime]

theorem tangent_eq_of_mkQ_eq {S : Type} [CommRing S] [CharP S p] (j : Zp2 p →+* S)
    (X : FormalODModule p S) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (m m' : CartierModule p X.F)
    (h : (X.toGradedCartierModuleData j hc).vRange.mkQ m = (X.toGradedCartierModuleData j hc).vRange.mkQ m') :
    tangent m = tangent m' := by
  have h1 : m - m' ∈ (X.toGradedCartierModuleData j hc).vRange := (Submodule.Quotient.eq _).1 h
  obtain ⟨y, hy⟩ := h1
  have hy' : verschiebung y = m - m' := by
    rw [← verschiebungInt_apply_eq_verschiebung]; exact hy
  have h2 : tangent (m - m') = 0 :=
    (MvFormalGroup.CartierModule.tangent_eq_zero_iff_exists_verschiebung_eq p X.F (m - m')).2 ⟨y, hy'⟩
  rwa [map_sub, sub_eq_zero] at h2

theorem locHom_injective {κ : Type} [Field κ] (x : PrimeSpectrum κ) :
    Function.Injective (Rigidified.locHom x) := by
  refine IsLocalization.injective (M := x.asIdeal.primeCompl) (Rigidified.Bloc x) ?_
  intro b hb
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rintro rfl
  exact hb (Submodule.zero_mem _)

theorem awayToLoc_awayHom {B : Type} [CommRing B] (x : PrimeSpectrum B) (f : B) (hf : f ∉ x.asIdeal) (b : B) :
    Rigidified.awayToLoc x f hf (Rigidified.awayHom f b) = Rigidified.locHom x b := by
  unfold Rigidified.awayToLoc
  exact IsLocalization.Away.lift_eq f _ b

theorem awayHom_one_surjective {κ : Type} [Field κ] : Function.Surjective (Rigidified.awayHom (1 : κ)) := by
  have hM : Submonoid.powers (1 : κ) ≤ IsUnit.submonoid κ := by
    rintro x ⟨n, rfl⟩; simp
  exact (IsLocalization.atUnits (R := κ) (M := Submonoid.powers (1 : κ)) (S := Rigidified.Baway (1 : κ)) hM).surjective

end K3cKit

end

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.FormalODModule

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ] (ψ : WittVector p k →+* κ)
    (t : Rigidified p Φ κ)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (τ₀ : Q.T₀ ≃ₗ[κ] ↥(t.X.lieZero (structureMap ι ψ)))
    (τ₁ : Q.T₁ ≃ₗ[κ] ↥(t.X.lieOne (structureMap ι ψ)))
    (hQ : t.IsCartierQuadrupleVia ι hcΦ rΦ ψ Q τ₀ τ₁)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : κ)))
    (L : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) (hL : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).IsCanonicalLMap L)
    (x : PrimeSpectrum κ) (m : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M) (v : Fin 2 → ℚ_[p])
    (hsec : t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL 1 (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0)) v) :
    ∃ (hv : v ∈ Q.N₁ x) (s : Q.T₁) (b : ↥(x.asIdeal.primeCompl)),
      Q.u₁ x ((1 : Rigidified.Bloc x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₁ x))) = LocalizedModule.mk s b ∧
      IsUnit (Rigidified.awayHom (1 : κ) (b : κ)) ∧
      ∀ l : Fin 2, Rigidified.awayHom (1 : κ) (((τ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) l) =
        Rigidified.awayHom (1 : κ) (b : κ) * MvFormalGroup.CartierModule.tangent m l := by

  classical

  have hM1 : Submonoid.powers (1 : κ) ≤ IsUnit.submonoid κ := by
    rintro y ⟨n, rfl⟩; simp
  haveI hnt : Nontrivial (Rigidified.Baway (1 : κ)) :=
    (IsLocalization.atUnits (R := κ) (M := Submonoid.powers (1 : κ)) (S := Rigidified.Baway (1 : κ)) hM1).injective.nontrivial
  haveI : CharP (Rigidified.Baway (1 : κ)) p :=
    charP_of_injective_algebraMap (algebraMap κ (Rigidified.Baway (1 : κ))).injective p

  obtain ⟨-, -, -, hNu⟩ := hQ
  obtain ⟨-, hN1, -, hu1⟩ := hNu hOD x
  have h1 : (1 : κ) ∉ x.asIdeal := (Ideal.ne_top_iff_one x.asIdeal).1 x.isPrime.ne_top
  have hv : v ∈ Q.N₁ x := (hN1 v).2 ⟨1, h1, hc, hcb, hcΦg, L, hL, _, hsec⟩
  obtain ⟨m₁, s, b, hm₁, hu, htan⟩ := hu1 v hv 1 h1 hc hcb hcΦg L hL _ hsec
  refine ⟨hv, s, b, hu, ?_, ?_⟩
  ·
    have hb0 : (b : κ) ≠ 0 := by
      intro hb
      exact b.2 (by rw [hb]; exact Submodule.zero_mem _)
    exact (isUnit_iff_ne_zero.2 hb0).map _
  ·
    have htm : tangent m₁ = tangent m := by
      refine K3cKit.tangent_eq_of_mkQ_eq (p := p) (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (t.XS (Rigidified.awayHom (1 : κ))) hc m₁ m ?_
      rw [hm₁]
      rfl
    intro l
    obtain ⟨c, hcm⟩ := K3cKit.awayHom_one_surjective (κ := κ) (tangent m l)
    have h3 := htan l
    rw [htm, ← hcm, K3cKit.awayToLoc_awayHom, ← map_mul] at h3
    have h4 : ((τ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) l = (b : κ) * c :=
      K3cKit.locHom_injective x h3
    rw [h4, map_mul, hcm]

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_uOne_eq_mk_and_awayHom_tauOne_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_uOne_eq_mk_and_awayHom_tauOne_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one (solution)
