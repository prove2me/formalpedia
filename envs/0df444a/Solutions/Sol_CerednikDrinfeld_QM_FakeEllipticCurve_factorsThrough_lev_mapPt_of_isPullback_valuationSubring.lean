-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_mapPt_of_isPullback_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/6525de2f-2d76-5b33-bd99-bbd6304fb48a

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_AlgebraicGeometry_existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_mapPt_of_isPullback_valuationSubring

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ))
    (𝒜 𝒟 : FakeEllipticCurve Λ N ↥O) (E d : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_lev : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t' E.f),
      FactorsThrough E.lev P ↔ ∃ P₀ : T ⟶ 𝒜.C, P₀ ≫ 𝒜.lev = P.1 ≫ gE)
    (gd : d.A ⟶ 𝒟.A) (hgd : CategoryTheory.IsPullback gd d.f 𝒟.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgd_lev : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t' d.f),
      FactorsThrough d.lev P ↔ ∃ P₀ : T ⟶ 𝒟.C, P₀ ≫ 𝒟.lev = P.1 ≫ gd)
    (φ : E.A ⟶ d.A) (hφ : φ ≫ d.f = E.f)
    (hφ_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough d.lev (mapPt φ hφ P))
    (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f) (hext : gE ≫ Φ = φ ≫ gd) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
      FactorsThrough 𝒜.lev P → FactorsThrough 𝒟.lev (mapPt Φ hΦ P) := by
  intro T t P hP
  haveI : Flat (𝒜.lev ≫ 𝒜.f) := 𝒜.lev_flat
  haveI : IsClosedImmersion 𝒟.lev := 𝒟.lev_closed

  have hι : Spec.map (CommRingCat.ofHom (algebraMap ↥O (AlgebraicClosure ℚ))) =
      Spec.map (CommRingCat.ofHom O.subtype) := rfl

  let ι₀ := Spec.map (CommRingCat.ofHom (algebraMap ↥O (AlgebraicClosure ℚ)))
  let W := pullback (𝒜.lev ≫ 𝒜.f) ι₀
  let a : W ⟶ 𝒜.A := pullback.fst (𝒜.lev ≫ 𝒜.f) ι₀ ≫ 𝒜.lev
  let b : W ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)) := pullback.snd (𝒜.lev ≫ 𝒜.f) ι₀
  have hab : a ≫ 𝒜.f = b ≫ Spec.map (CommRingCat.ofHom O.subtype) := by
    rw [← hι]; simp only [a, b, Category.assoc]; exact pullback.condition
  let P₁ : W ⟶ E.A := hgE.lift a b hab
  have hP₁g : P₁ ≫ gE = a := hgE.lift_fst _ _ _
  have hP₁f : P₁ ≫ E.f = b := hgE.lift_snd _ _ _
  let Pg : SchemeHomOver b E.f := ⟨P₁, hP₁f⟩
  have hPg : FactorsThrough E.lev Pg :=
    (hgE_lev b Pg).2 ⟨pullback.fst (𝒜.lev ≫ 𝒜.f) ι₀, by rw [hP₁g]⟩
  have hQ := hφ_lev b Pg hPg
  obtain ⟨R₀, hR₀⟩ := (hgd_lev b (mapPt φ hφ Pg)).1 hQ

  have hψK : R₀ ≫ 𝒟.lev = pullback.fst (𝒜.lev ≫ 𝒜.f) ι₀ ≫ (𝒜.lev ≫ Φ) := by
    rw [hR₀]
    show (P₁ ≫ φ) ≫ gd = pullback.fst (𝒜.lev ≫ 𝒜.f) ι₀ ≫ (𝒜.lev ≫ Φ)
    rw [Category.assoc, ← hext, ← Category.assoc, hP₁g]
    simp only [a, Category.assoc]
  obtain ⟨ψ, hψ, -⟩ := AlgebraicGeometry.existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq
    (AlgebraicClosure ℚ) (𝒜.lev ≫ 𝒜.f) 𝒟.lev (𝒜.lev ≫ Φ) R₀ hψK
  obtain ⟨P₀, hP₀⟩ := hP
  refine ⟨P₀ ≫ ψ, ?_⟩
  show (P₀ ≫ ψ) ≫ 𝒟.lev = P.1 ≫ Φ
  rw [Category.assoc, hψ, ← Category.assoc, hP₀]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_mapPt_of_isPullback_valuationSubring
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_mapPt_of_isPullback_valuationSubring (solution)
