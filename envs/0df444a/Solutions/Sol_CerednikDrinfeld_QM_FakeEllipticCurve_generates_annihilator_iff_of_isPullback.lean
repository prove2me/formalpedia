-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.generates_annihilator_iff_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c36d5763-39f4-5eeb-93a4-d1993f415508

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_generates_annihilator_iff_of_isPullback

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open GoodReductionJacobian

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ)
    (R' L : Type) [CommRing R'] [CommRing L] (φ : R' →+* L)
    (E' : FakeEllipticCurve Λ N R') (P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) E'.f)
    (E : FakeEllipticCurve Λ N L) (gL : E.A ⟶ E'.A)
    (hgL : CategoryTheory.IsPullback gL E.f E'.f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ gL =
          (E'.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨P.1 ≫ gL, by rw [Category.assoc, hgL.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ gL, by rw [Category.assoc, hgL.w, ← Category.assoc, Q.2]⟩).1)
    (hact : ∀ x : ↥Λ, E.act x ≫ gL = gL ≫ E'.act x)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) E.f) (hP : P.1 ≫ gL = Spec.map (CommRingCat.ofHom φ) ≫ P'.1)
    (k : Type) [Field k] [IsAlgClosed k] (sk : L →+* k) :
    ((∀ Q : SchemeHomOver (geomPoint k sk) E.f,
        nsmulPt E.L (geomPoint k sk) m Q = E.L.one (geomPoint k sk) →
          ∃ x : ↥Λ, pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k sk) = Q) ∧
     (∀ x : ↥Λ, pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k sk) = E.L.one (geomPoint k sk) ↔
        ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]))) ↔
    ((∀ Q : SchemeHomOver (geomPoint k (sk.comp φ)) E'.f,
        nsmulPt E'.L (geomPoint k (sk.comp φ)) m Q = E'.L.one (geomPoint k (sk.comp φ)) →
          ∃ x : ↥Λ, pushPt (E'.act x) (E'.act_over x) (FakeEllipticCurve.sectionAt P' k (sk.comp φ)) = Q) ∧
     (∀ x : ↥Λ, pushPt (E'.act x) (E'.act_over x) (FakeEllipticCurve.sectionAt P' k (sk.comp φ)) = E'.L.one (geomPoint k (sk.comp φ)) ↔
        ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]))) := by
  classical

  have hfac : geomPoint k (sk.comp φ) = geomPoint k sk ≫ Spec.map (CommRingCat.ofHom φ) := by
    change Spec.map (CommRingCat.ofHom (sk.comp φ)) = Spec.map (CommRingCat.ofHom sk) ≫ Spec.map (CommRingCat.ofHom φ)
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  suffices key : ∀ (γ' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R'))
      (hγ' : γ' = geomPoint k sk ≫ Spec.map (CommRingCat.ofHom φ)) (c' : γ' ≫ 𝟙 _ = γ'),
      ((∀ Q : SchemeHomOver (geomPoint k sk) E.f,
        nsmulPt E.L (geomPoint k sk) m Q = E.L.one (geomPoint k sk) →
          ∃ x : ↥Λ, pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k sk) = Q) ∧
     (∀ x : ↥Λ, pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k sk) = E.L.one (geomPoint k sk) ↔
        ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]))) ↔
      ((∀ Q : SchemeHomOver γ' E'.f,
        nsmulPt E'.L γ' m Q = E'.L.one γ' →
          ∃ x : ↥Λ, pushPt (E'.act x) (E'.act_over x) (GoodReductionJacobian.schemeHomOverComp γ' c' P') = Q) ∧
     (∀ x : ↥Λ, pushPt (E'.act x) (E'.act_over x) (GoodReductionJacobian.schemeHomOverComp γ' c' P') = E'.L.one γ' ↔
        ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]))) by
    exact key (geomPoint k (sk.comp φ)) hfac (Category.comp_id _)
  intro γ' hγ' c'
  subst hγ'
  unfold FakeEllipticCurve.sectionAt
  set γ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of L) := geomPoint k sk with hγ
  set γ' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R') := γ ≫ Spec.map (CommRingCat.ofHom φ) with hγ'

  let Φ : SchemeHomOver γ E.f → SchemeHomOver γ' E'.f := fun Q =>
    ⟨Q.1 ≫ gL, by rw [hγ', Category.assoc, hgL.w, ← Category.assoc, Q.2]⟩
  have Φ_coe : ∀ Q : SchemeHomOver γ E.f, (Φ Q).1 = Q.1 ≫ gL := fun Q => rfl
  have Φ_inj : Function.Injective Φ := by
    intro Q₁ Q₂ h
    apply Subtype.ext
    apply hgL.hom_ext
    · exact congrArg Subtype.val h
    · rw [Q₁.2, Q₂.2]
  have Φ_surj : Function.Surjective Φ := by
    intro Q'
    refine ⟨⟨hgL.lift Q'.1 γ (by rw [Q'.2, hγ']), hgL.lift_snd _ _ _⟩, ?_⟩
    apply Subtype.ext
    exact hgL.lift_fst _ _ _
  have Φ_mul : ∀ Q₁ Q₂ : SchemeHomOver γ E.f, Φ (E.L.mul γ Q₁ Q₂) = E'.L.mul γ' (Φ Q₁) (Φ Q₂) := by
    intro Q₁ Q₂
    apply Subtype.ext
    exact hmul γ Q₁ Q₂
  have Φ_one : Φ (E.L.one γ) = E'.L.one γ' := by
    letI := E'.L.pointGroup γ'
    have h : E'.L.mul γ' (Φ (E.L.one γ)) (Φ (E.L.one γ)) = Φ (E.L.one γ) := by
      rw [← Φ_mul, E.L.one_mul]

    have : Φ (E.L.one γ) * Φ (E.L.one γ) = Φ (E.L.one γ) * 1 := by rw [mul_one]; exact h
    exact mul_left_cancel this
  have Φ_nsmul : ∀ (n : ℕ) (Q : SchemeHomOver γ E.f), Φ (nsmulPt E.L γ n Q) = nsmulPt E'.L γ' n (Φ Q) := by
    intro n Q
    induction n with
    | zero => exact Φ_one
    | succ n ih =>
      show Φ (E.L.mul γ (nsmulPt E.L γ n Q) Q) = E'.L.mul γ' (nsmulPt E'.L γ' n (Φ Q)) (Φ Q)
      rw [Φ_mul, ih]
  have Φ_act : ∀ (x : ↥Λ) (Q : SchemeHomOver γ E.f),
      Φ (pushPt (E.act x) (E.act_over x) Q) = pushPt (E'.act x) (E'.act_over x) (Φ Q) := by
    intro x Q
    apply Subtype.ext
    change (Q.1 ≫ E.act x) ≫ gL = (Q.1 ≫ gL) ≫ E'.act x
    rw [Category.assoc, hact, Category.assoc]
  have Φ_sec : Φ (GoodReductionJacobian.schemeHomOverComp γ (Category.comp_id γ) P) =
      GoodReductionJacobian.schemeHomOverComp γ' c' P' := by
    apply Subtype.ext
    change (γ ≫ P.1) ≫ gL = γ' ≫ P'.1
    rw [Category.assoc, hP, hγ', Category.assoc]
  have Φ_tors : ∀ Q : SchemeHomOver γ E.f,
      nsmulPt E.L γ m Q = E.L.one γ ↔ nsmulPt E'.L γ' m (Φ Q) = E'.L.one γ' := by
    intro Q
    rw [← Φ_nsmul, ← Φ_one]
    exact ⟨fun h => by rw [h], fun h => Φ_inj h⟩

  constructor
  · rintro ⟨hgen, hann⟩
    refine ⟨?_, ?_⟩
    · intro Q' hQ'
      obtain ⟨Q, rfl⟩ := Φ_surj Q'
      obtain ⟨x, hx⟩ := hgen Q ((Φ_tors Q).2 hQ')
      exact ⟨x, by rw [← Φ_sec, ← Φ_act, hx]⟩
    · intro x
      rw [← hann x, ← Φ_sec, ← Φ_act, ← Φ_one]
      exact ⟨fun h => Φ_inj h, fun h => by rw [h]⟩
  · rintro ⟨hgen, hann⟩
    refine ⟨?_, ?_⟩
    · intro Q hQ
      obtain ⟨x, hx⟩ := hgen (Φ Q) ((Φ_tors Q).1 hQ)
      exact ⟨x, Φ_inj (by rw [Φ_act, Φ_sec, hx])⟩
    · intro x
      rw [← hann x, ← Φ_sec, ← Φ_act, ← Φ_one]
      exact ⟨fun h => by rw [h], fun h => Φ_inj h⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_generates_annihilator_iff_of_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_generates_annihilator_iff_of_isPullback (solution)
