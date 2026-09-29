-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_corr_of_isoVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/2bf7f76b-cc5c-58b0-9aa7-356128d164ac

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isoVia

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace P3RigIso

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
variable (L : GoodReductionJacobian.RelativeGroupLaw R f)

theorem mul_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (ht : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]

end P3RigIso

open P3RigIso in
theorem solution
    {r N : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E E' : FakeEllipticCurve Λ N B}
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (hvia : FakeEllipticCurve.IsoVia E E' i hi) :
    ∃ (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψ E')
      (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (_ : ib ≫ ϱ'.gb = ϱ.gb ≫ i.hom) (_ : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
      (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (_ : uA ≫ ϱ.gA = ϱ'.gA)
      (i₁ j₁ : ℕ),
      ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  obtain ⟨hsqb, bmul, bact, blev⟩ := ϱ.isPullback_Eb
  obtain ⟨imul, iact, ilev⟩ := hvia

  have sqi : IsPullback i.hom E.f E'.f (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [hi, Category.comp_id]⟩
  have hsq' : IsPullback (ϱ.gb ≫ i.hom) ϱ.Eb.f E'.f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})))) := by
    have h := hsqb.paste_horiz sqi
    rwa [Category.comp_id] at h
  have hEb' : FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) E' ϱ.Eb (ϱ.gb ≫ i.hom) := by
    refine ⟨hsq', ?_, ?_, ?_⟩
    · intro T t' P Q
      rw [← Category.assoc, bmul]
      have h := congrArg Subtype.val (imul (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))))
        ⟨P.1 ≫ ϱ.gb, by rw [Category.assoc, hsqb.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ ϱ.gb, by rw [Category.assoc, hsqb.w, ← Category.assoc, Q.2]⟩)
      rw [mapPt_coe] at h
      rw [h]
      exact mul_val_congr E'.L rfl _ _ _ _ (by simp only [mapPt_coe, Category.assoc]) (by simp only [mapPt_coe, Category.assoc])
    · intro x
      rw [← Category.assoc, bact, Category.assoc, iact, Category.assoc]
    · intro T t' P hP
      obtain ⟨P₀, hP₀⟩ := blev t' P hP
      obtain ⟨P₁, hP₁⟩ := (ilev (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))))
        ⟨P.1 ≫ ϱ.gb, by rw [Category.assoc, hsqb.w, ← Category.assoc, P.2]⟩).mp ⟨P₀, hP₀⟩
      exact ⟨P₁, by rw [hP₁]; simp only [mapPt_coe, Category.assoc]⟩

  have hS : Spec.map (CommRingCat.ofHom (RingHom.id (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
  have hidA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ.Ab (𝟙 _) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hS]
      exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
    · intro T t P Q
      rw [Category.comp_id]
      exact mul_val_congr ϱ.Ab.L (by rw [hS, Category.comp_id]) _ _ _ _ (Category.comp_id _).symm (Category.comp_id _).symm
    · intro x
      rw [Category.id_comp, Category.comp_id]
    · intro T t P hP
      obtain ⟨P₀, hP₀⟩ := hP
      exact ⟨P₀, by rw [hP₀, Category.comp_id]⟩
  refine ⟨{ Eb := ϱ.Eb, gb := ϱ.gb ≫ i.hom, isPullback_Eb := hEb', Ab := ϱ.Ab, gA := ϱ.gA, isPullback_Ab := ϱ.isPullback_Ab,
            d := ϱ.d, φ := ϱ.φ, φ' := ϱ.φ', φ_over := ϱ.φ_over, isIsogenyPair := ϱ.isIsogenyPair, preservesLevel := ϱ.preservesLevel },
          𝟙 _, ?_, ?_, 𝟙 _, hidA, ?_, 0, 0, ?_⟩
  · exact Category.id_comp _
  · exact Category.id_comp _
  · exact Category.id_comp _
  · simp only [Category.id_comp]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isoVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isoVia (solution)
