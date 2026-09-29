-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogenyPair.comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e2a1aa9a-96e8-5e89-a382-c1fa3cb1e9c1

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsIsogenyPair_comp

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {d₁ d₂ : ℕ} {E E' E'' : FakeEllipticCurve Λ N S}
    {f : E.A ⟶ E'.A} {f' : E'.A ⟶ E.A} {g : E'.A ⟶ E''.A} {g' : E''.A ⟶ E'.A}
    (hf : FakeEllipticCurve.IsIsogenyPair d₁ E E' f f') (hg : FakeEllipticCurve.IsIsogenyPair d₂ E' E'' g g') :
    FakeEllipticCurve.IsIsogenyPair (d₁ * d₂) E E'' (f ≫ g) (g' ≫ f')  := by
  obtain ⟨hf0, hf'0, hfhom, hf'hom, hflin, hf'lin, hfdeg⟩ := hf
  obtain ⟨hg0, hg'0, hghom, hg'hom, hglin, hg'lin, hgdeg⟩ := hg
  have hfg0 : (f ≫ g) ≫ E''.f = E.f := by rw [Category.assoc, hg0, hf0]
  have hgf0 : (g' ≫ f') ≫ E.f = E''.f := by rw [Category.assoc, hf'0, hg'0]

  have mapPt_comp : ∀ {A₁ A₂ A₃ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of S)} {f₂ : A₂ ⟶ Spec (CommRingCat.of S)}
      {f₃ : A₃ ⟶ Spec (CommRingCat.of S)} (u : A₁ ⟶ A₂) (hu : u ≫ f₂ = f₁) (v : A₂ ⟶ A₃) (hv : v ≫ f₃ = f₂)
      (huv : (u ≫ v) ≫ f₃ = f₁) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f₁),
      mapPt (u ≫ v) huv P = mapPt v hv (mapPt u hu P) := by
    intro A₁ A₂ A₃ f₁ f₂ f₃ u hu v hv huv T t P
    apply Subtype.ext
    show P.1 ≫ (u ≫ v) = (P.1 ≫ u) ≫ v
    rw [Category.assoc]
  have h1 : ((d₁ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ d₁
  have h2 : ((d₂ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ d₂
  refine ⟨hfg0, hgf0, fun t P Q => ?_, fun t P Q => ?_, fun x => ?_, fun x => ?_, fun hd => ?_⟩
  · rw [mapPt_comp f hf0 g hg0 hfg0, mapPt_comp f hf0 g hg0 hfg0, mapPt_comp f hf0 g hg0 hfg0, hfhom, hghom]
  · rw [mapPt_comp g' hg'0 f' hf'0 hgf0, mapPt_comp g' hg'0 f' hf'0 hgf0, mapPt_comp g' hg'0 f' hf'0 hgf0, hg'hom, hf'hom]
  · rw [← Category.assoc, hflin, Category.assoc, hglin, Category.assoc]
  · rw [← Category.assoc, hg'lin, Category.assoc, hf'lin, Category.assoc]
  · have hcomm : ((⟨((d₂ : ℕ) : ℚ), h2⟩ : ↥Λ) : ℍ[ℚ, a, b]) * ((⟨((d₁ : ℕ) : ℚ), h1⟩ : ↥Λ) : ℍ[ℚ, a, b]) = (((d₁ * d₂ : ℕ) : ℚ) : ℍ[ℚ, a, b]) := by
      show (((d₂ : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (((d₁ : ℕ) : ℚ) : ℍ[ℚ, a, b]) = (((d₁ * d₂ : ℕ) : ℚ) : ℍ[ℚ, a, b])
      push_cast
      exact Nat.cast_comm _ _
    have hd21 : ((⟨((d₂ : ℕ) : ℚ), h2⟩ : ↥Λ) : ℍ[ℚ, a, b]) * ((⟨((d₁ : ℕ) : ℚ), h1⟩ : ↥Λ) : ℍ[ℚ, a, b]) ∈ Λ := by
      rw [hcomm]; exact hd
    have hcomm' : ((⟨((d₁ : ℕ) : ℚ), h1⟩ : ↥Λ) : ℍ[ℚ, a, b]) * ((⟨((d₂ : ℕ) : ℚ), h2⟩ : ↥Λ) : ℍ[ℚ, a, b]) = (((d₁ * d₂ : ℕ) : ℚ) : ℍ[ℚ, a, b]) := by
      show (((d₁ : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (((d₂ : ℕ) : ℚ) : ℍ[ℚ, a, b]) = (((d₁ * d₂ : ℕ) : ℚ) : ℍ[ℚ, a, b])
      push_cast
      rfl
    have hd12 : ((⟨((d₁ : ℕ) : ℚ), h1⟩ : ↥Λ) : ℍ[ℚ, a, b]) * ((⟨((d₂ : ℕ) : ℚ), h2⟩ : ↥Λ) : ℍ[ℚ, a, b]) ∈ Λ := by
      rw [hcomm']; exact hd
    have hmul : (⟨((d₁ * d₂ : ℕ) : ℚ), hd⟩ : ↥Λ) =
        ⟨((⟨((d₂ : ℕ) : ℚ), h2⟩ : ↥Λ) : ℍ[ℚ, a, b]) * ((⟨((d₁ : ℕ) : ℚ), h1⟩ : ↥Λ) : ℍ[ℚ, a, b]), hd21⟩ :=
      Subtype.ext hcomm.symm
    have hmul' : (⟨((d₁ * d₂ : ℕ) : ℚ), hd⟩ : ↥Λ) =
        ⟨((⟨((d₁ : ℕ) : ℚ), h1⟩ : ↥Λ) : ℍ[ℚ, a, b]) * ((⟨((d₂ : ℕ) : ℚ), h2⟩ : ↥Λ) : ℍ[ℚ, a, b]), hd12⟩ :=
      Subtype.ext hcomm'.symm
    constructor
    ·
      rw [Category.assoc, ← Category.assoc g, (hgdeg h2).1, hf'lin, ← Category.assoc, (hfdeg h1).1, hmul, E.act_mul]
    · rw [Category.assoc, ← Category.assoc f', (hfdeg h1).2, hglin, ← Category.assoc, (hgdeg h2).2, hmul', E''.act_mul]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_IsIsogenyPair_comp
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsIsogenyPair_comp (solution)
