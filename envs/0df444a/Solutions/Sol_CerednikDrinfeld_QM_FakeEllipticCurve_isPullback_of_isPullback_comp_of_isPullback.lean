-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isPullback_of_isPullback_comp_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/fa872a0c-4f3d-5d69-9884-24137fc84c61

import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_of_isPullback_comp_of_isPullback

set_option autoImplicit false

universe u

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM

namespace DescPBAux

theorem mul_val_congr {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f) (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst h
  obtain ⟨x₁, _⟩ := x₁; obtain ⟨x₂, _⟩ := x₂; obtain ⟨y₁, _⟩ := y₁; obtain ⟨y₂, _⟩ := y₂
  simp only at hx hy
  subst hx hy
  rfl

end DescPBAux

open DescPBAux in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S₀ S₁ S₂ : Type u} [CommRing S₀] [CommRing S₁] [CommRing S₂]
    (j : S₀ →+* S₁) (ι : S₁ →+* S₂)
    (E₀ : FakeEllipticCurve Λ N S₀) (E₁ : FakeEllipticCurve Λ N S₁) (E₂ : FakeEllipticCurve Λ N S₂)
    (h₀₂ : FakeEllipticCurve.IsPullback (ι.comp j) E₀ E₂) (h₀₁ : FakeEllipticCurve.IsPullback j E₀ E₁) :
    FakeEllipticCurve.IsPullback ι E₁ E₂ := by
  obtain ⟨g₀₂, hg₀₂, hmul₀₂, hact₀₂, hlev₀₂⟩ := h₀₂
  obtain ⟨g₀₁, hg₀₁, hmul₀₁, hact₀₁, hlev₀₁⟩ := h₀₁
  have hSpec : Spec.map (CommRingCat.ofHom (ι.comp j)) =
      Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom j) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hw : g₀₂ ≫ E₀.f = (E₂.f ≫ Spec.map (CommRingCat.ofHom ι)) ≫ Spec.map (CommRingCat.ofHom j) := by
    rw [hg₀₂.w, hSpec, Category.assoc]

  let g₁₂ : E₂.A ⟶ E₁.A := hg₀₁.lift g₀₂ (E₂.f ≫ Spec.map (CommRingCat.ofHom ι)) hw
  have h12_01 : g₁₂ ≫ g₀₁ = g₀₂ := hg₀₁.lift_fst _ _ hw
  have h12_f : g₁₂ ≫ E₁.f = E₂.f ≫ Spec.map (CommRingCat.ofHom ι) := hg₀₁.lift_snd _ _ hw

  have hbig : IsPullback (g₁₂ ≫ g₀₁) E₂.f E₀.f (Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom j)) := by
    rw [h12_01, ← hSpec]; exact hg₀₂
  have hg₁₂ : IsPullback g₁₂ E₂.f E₁.f (Spec.map (CommRingCat.ofHom ι)) := IsPullback.of_right hbig h12_f hg₀₁
  refine ⟨g₁₂, hg₁₂, ?_, ?_, ?_⟩
  ·
    intro T t' P Q
    apply hg₀₁.hom_ext
    · rw [Category.assoc, h12_01, hmul₀₂, hmul₀₁]
      exact mul_val_congr E₀.L (by rw [Category.assoc, hSpec]) _ _ _ _
        (by simp only [Category.assoc, h12_01]) (by simp only [Category.assoc, h12_01])
    · rw [Category.assoc, h12_f, ← Category.assoc, (E₂.L.mul t' P Q).2,
        (E₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom ι)) _ _).2]
  ·
    intro x
    apply hg₀₁.hom_ext
    · rw [Category.assoc, h12_01, hact₀₂, Category.assoc, hact₀₁, ← Category.assoc, h12_01]
    · rw [Category.assoc, h12_f, ← Category.assoc, E₂.act_over, Category.assoc, E₁.act_over, h12_f]
  ·
    intro T t' P hP
    obtain ⟨P₀, hP₀⟩ := hlev₀₂ t' P hP
    let P₁ : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom ι)) E₁.f :=
      ⟨P.1 ≫ g₁₂, by rw [Category.assoc, h12_f, ← Category.assoc, P.2]⟩
    exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback
      j E₀ E₁ g₀₁ hg₀₁ hmul₀₁ hlev₀₁ (t' ≫ Spec.map (CommRingCat.ofHom ι)) P₁
      ⟨P₀, by rw [hP₀]; change _ = (P.1 ≫ g₁₂) ≫ g₀₁; rw [Category.assoc, h12_01]⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_of_isPullback_comp_of_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_of_isPullback_comp_of_isPullback (solution)
