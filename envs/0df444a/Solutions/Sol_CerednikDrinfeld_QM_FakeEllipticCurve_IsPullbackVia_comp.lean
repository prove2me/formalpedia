-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/461593d8-e4f0-567b-b292-70cb1b325133

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

open IsLocalRing

namespace V2Aux

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f)
    (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain ⟨p₁, hp₁⟩ := P₁
  obtain ⟨p₂, hp₂⟩ := P₂
  obtain ⟨q₁, hq₁⟩ := Q₁
  obtain ⟨q₂, hq₂⟩ := Q₂
  simp only at hP hQ
  subst hP
  subst hQ
  rfl

end V2Aux

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (E'' : FakeEllipticCurve Λ N S'')
    (g : E'.A ⟶ E.A) (g' : E''.A ⟶ E'.A)
    (hg : FakeEllipticCurve.IsPullbackVia φ E E' g) (hg' : FakeEllipticCurve.IsPullbackVia ψ E' E'' g') :
    FakeEllipticCurve.IsPullbackVia (ψ.comp φ) E E'' (g' ≫ g) := by
  obtain ⟨hsq, hlaw, hact, hlev⟩ := hg
  obtain ⟨hsq', hlaw', hact', hlev'⟩ := hg'
  have hsp : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp]; rfl
  have hsq'' : IsPullback (g' ≫ g) E''.f E.f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) := by
    rw [hsp]; exact hsq'.paste_horiz hsq
  refine ⟨hsq'', ?_, ?_, ?_⟩
  · intro T t'' P Q
    have e1 := hlaw' t'' P Q
    have e2 := hlaw (t'' ≫ Spec.map (CommRingCat.ofHom ψ))
      ⟨P.1 ≫ g', by rw [Category.assoc, hsq'.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ g', by rw [Category.assoc, hsq'.w, ← Category.assoc, Q.2]⟩
    rw [← Category.assoc, e1, e2]
    apply V2Aux.mul_val_congr
    · rw [Category.assoc, ← hsp]
    · simp only [Category.assoc]
    · simp only [Category.assoc]
  · intro x
    rw [← Category.assoc, hact' x, Category.assoc, hact x, Category.assoc]
  · intro T t'' P hP
    obtain ⟨P₁, hP₁⟩ := hlev' t'' P hP
    obtain ⟨P₀, hP₀⟩ := hlev (t'' ≫ Spec.map (CommRingCat.ofHom ψ))
      ⟨P.1 ≫ g', by rw [Category.assoc, hsq'.w, ← Category.assoc, P.2]⟩ ⟨P₁, hP₁⟩
    exact ⟨P₀, by rw [hP₀]; simp only [Category.assoc]⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp (solution)
