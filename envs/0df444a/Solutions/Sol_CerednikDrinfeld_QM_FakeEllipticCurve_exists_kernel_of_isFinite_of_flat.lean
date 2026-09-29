-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernel_of_isFinite_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/1ee8f818-df22-56f1-89bf-a2ff24da8a2b

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernel_of_isFinite_of_flat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type u} [CommRing S] (𝒜 𝒟 : FakeEllipticCurve Λ N S)
    (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f) [IsFinite Φ] [Flat Φ] [LocallyOfFinitePresentation Φ] :
    ∃ (Kk : Scheme.{u}) (ι : Kk ⟶ 𝒜.A),
      IsClosedImmersion ι ∧ IsFinite (ι ≫ 𝒜.f) ∧ Flat (ι ≫ 𝒜.f) ∧ LocallyOfFinitePresentation (ι ≫ 𝒜.f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t 𝒜.f),
        FactorsThrough ι P ↔ mapPt Φ hΦ P = 𝒟.L.one t) ∧
      (∀ s : ↥(Spec (CommRingCat.of S)),
        (ι ≫ 𝒜.f).finrank s = Φ.finrank ((𝒟.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base s)) := by
  haveI : IsProper 𝒟.f := 𝒟.bundle.proper
  let e : Spec (CommRingCat.of S) ⟶ 𝒟.A := (𝒟.L.one (𝟙 (Spec (CommRingCat.of S)))).1
  have he : e ≫ 𝒟.f = 𝟙 _ := (𝒟.L.one (𝟙 (Spec (CommRingCat.of S)))).2
  haveI : IsClosedImmersion (e ≫ 𝒟.f) := by rw [he]; infer_instance
  haveI : IsClosedImmersion e := IsClosedImmersion.of_comp e 𝒟.f
  let ι := pullback.fst Φ e
  have hιf : ι ≫ 𝒜.f = pullback.snd Φ e := by
    rw [← hΦ, ← Category.assoc, pullback.condition, Category.assoc, he, Category.comp_id]
  refine ⟨pullback Φ e, ι, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hιf]; infer_instance
  · rw [hιf]; infer_instance
  · rw [hιf]; infer_instance
  · intro T t P
    have hone : (𝒟.L.one t).1 = t ≫ e := by
      rw [← 𝒟.L.one_natural (𝟙 _) t t (Category.comp_id t)]; rfl
    constructor
    · rintro ⟨P₀, hP₀⟩
      apply Subtype.ext
      show P.1 ≫ Φ = (𝒟.L.one t).1
      have ht : P₀ ≫ pullback.snd Φ e = t := by rw [← hιf, ← Category.assoc, hP₀, P.2]
      rw [hone, ← hP₀, Category.assoc, pullback.condition, ← Category.assoc, ht]
    · intro h
      have h' : P.1 ≫ Φ = t ≫ e := by rw [← hone]; exact congrArg Subtype.val h
      exact ⟨pullback.lift P.1 t h', pullback.lift_fst _ _ _⟩
  · intro s
    rw [hιf]
    exact Scheme.Hom.finrank_pullback_snd Φ e s

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernel_of_isFinite_of_flat
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernel_of_isFinite_of_flat (solution)
