-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isPullback_comp_of_isPullback_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/41dc02d8-a005-56d9-a257-4d09f2009a6a

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_comp_of_isPullback_of_isPullback

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S₀ S₁ S₂ : Type u} [CommRing S₀] [CommRing S₁] [CommRing S₂]
    (j : S₀ →+* S₁) (ι : S₁ →+* S₂)
    (E₀ : FakeEllipticCurve Λ N S₀) (E₁ : FakeEllipticCurve Λ N S₁) (E₂ : FakeEllipticCurve Λ N S₂)
    (h₀₁ : FakeEllipticCurve.IsPullback j E₀ E₁) (h₁₂ : FakeEllipticCurve.IsPullback ι E₁ E₂) :
    FakeEllipticCurve.IsPullback (ι.comp j) E₀ E₂ := by
  obtain ⟨g₁, hg₁, hmul₁, hact₁, hlev₁⟩ := h₀₁
  obtain ⟨g₂, hg₂, hmul₂, hact₂, hlev₂⟩ := h₁₂
  have hSpec : Spec.map (CommRingCat.ofHom (ι.comp j)) =
      Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom j) := by
    rw [← Spec.map_comp]; rfl
  have hg : CategoryTheory.IsPullback (g₂ ≫ g₁) E₂.f E₀.f (Spec.map (CommRingCat.ofHom (ι.comp j))) := by
    rw [hSpec]; exact hg₂.paste_horiz hg₁

  have mul_congr : ∀ {T : Scheme.{u}} {t t'' : T ⟶ Spec (CommRingCat.of S₀)} (_ : t = t'')
      (x y : SchemeHomOver t E₀.f) (x'' y'' : SchemeHomOver t'' E₀.f),
      x.1 = x''.1 → y.1 = y''.1 → (E₀.L.mul t x y).1 = (E₀.L.mul t'' x'' y'').1 := by
    rintro T t t'' rfl ⟨x, hx⟩ ⟨y, hy⟩ ⟨x'', hx''⟩ ⟨y'', hy''⟩ (rfl : x = x'') (rfl : y = y'')
    rfl
  refine ⟨g₂ ≫ g₁, hg, ?_, ?_, ?_⟩
  · intro T t' P Q
    rw [← Category.assoc, hmul₂ t' P Q, hmul₁ (t' ≫ Spec.map (CommRingCat.ofHom ι)) _ _]
    exact mul_congr (by rw [hSpec, Category.assoc]) _ _ _ _ (Category.assoc _ _ _) (Category.assoc _ _ _)
  · intro x
    rw [← Category.assoc, hact₂ x, Category.assoc, hact₁ x, Category.assoc]
  · intro T t' P hP
    obtain ⟨P₁, hP₁⟩ := hlev₂ t' P hP
    obtain ⟨P₀, hP₀⟩ := hlev₁ (P₁ ≫ E₁.lev ≫ E₁.f) ⟨P₁ ≫ E₁.lev, rfl⟩ ⟨P₁, rfl⟩
    exact ⟨P₀, by rw [hP₀]; show (P₁ ≫ E₁.lev) ≫ g₁ = P.1 ≫ g₂ ≫ g₁; rw [hP₁, Category.assoc]⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_comp_of_isPullback_of_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_comp_of_isPullback_of_isPullback (solution)
