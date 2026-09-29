-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_equiv_schemeHomOver_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/03f88612-cc97-5194-bbc8-63cc94fdf255

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_equiv_schemeHomOver_of_isPullback

set_option autoImplicit false

universe u

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace ChartPtsBody

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (G : GoodReductionJacobian.RelativeGroupLaw R f)

theorem mul_inv_cancel {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.mul t x (G.inv t x) = G.one t := by
  have h1 : G.mul t (G.inv t (G.inv t x)) (G.inv t x) = G.one t := G.inv_mul_cancel t _
  have h2 : G.mul t (G.inv t x) (G.mul t x (G.inv t x)) = G.inv t x := by
    rw [← G.mul_assoc, G.inv_mul_cancel, G.one_mul]
  calc G.mul t x (G.inv t x)
      = G.mul t (G.one t) (G.mul t x (G.inv t x)) := (G.one_mul t _).symm
    _ = G.mul t (G.mul t (G.inv t (G.inv t x)) (G.inv t x)) (G.mul t x (G.inv t x)) := by rw [h1]
    _ = G.mul t (G.inv t (G.inv t x)) (G.mul t (G.inv t x) (G.mul t x (G.inv t x))) := G.mul_assoc t _ _ _
    _ = G.mul t (G.inv t (G.inv t x)) (G.inv t x) := by rw [h2]
    _ = G.one t := h1

theorem eq_inv_of_mul_eq_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f)
    (h : G.mul t y x = G.one t) : y = G.inv t x := by
  calc y = G.mul t y (G.one t) := (G.mul_one t y).symm
    _ = G.mul t y (G.mul t x (G.inv t x)) := by rw [mul_inv_cancel]
    _ = G.mul t (G.mul t y x) (G.inv t x) := (G.mul_assoc t _ _ _).symm
    _ = G.inv t x := by rw [h, G.one_mul]

theorem eq_one_of_mul_self {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
    (h : G.mul t x x = x) : x = G.one t := by
  calc x = G.mul t (G.one t) x := (G.one_mul t x).symm
    _ = G.mul t (G.mul t (G.inv t x) x) x := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t x) (G.mul t x x) := G.mul_assoc t _ _ _
    _ = G.mul t (G.inv t x) x := by rw [h]
    _ = G.one t := G.inv_mul_cancel t x

end ChartPtsBody

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type u} [CommRing S] [CommRing S']
    (φ : S →+* S') (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S')
    (g : E'.A ⟶ E.A) (hg : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
    (hg_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t E'.f),
      (E'.L.mul t P Q).1 ≫ g =
        (E.L.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S')) :
    ∃ σ : SchemeHomOver t E'.f ≃ SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) E.f,
      (∀ P : SchemeHomOver t E'.f, (σ P).1 = P.1 ≫ g) ∧
      σ (E'.L.one t) = E.L.one _ ∧
      (∀ P Q : SchemeHomOver t E'.f, σ (E'.L.mul t P Q) = E.L.mul _ (σ P) (σ Q)) ∧
      (∀ P : SchemeHomOver t E'.f, σ (E'.L.inv t P) = E.L.inv _ (σ P)) ∧
      (∀ (n : ℕ) (P : SchemeHomOver t E'.f), σ (nsmulPt E'.L t n P) = nsmulPt E.L _ n (σ P)) ∧
      (∀ (x : ↥Λ) (P : SchemeHomOver t E'.f),
        σ (pushPt (E'.act x) (E'.act_over x) P) = pushPt (E.act x) (E.act_over x) (σ P)) := by

  let σ : SchemeHomOver t E'.f ≃ SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) E.f :=
    { toFun := fun P => ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
      invFun := fun Q => ⟨hg.lift Q.1 t Q.2, hg.lift_snd _ _ _⟩
      left_inv := fun P => by
        apply Subtype.ext
        apply hg.hom_ext
        · rw [hg.lift_fst]
        · rw [hg.lift_snd]; exact P.2.symm
      right_inv := fun Q => by
        apply Subtype.ext
        exact hg.lift_fst _ _ _ }
  have hσ : ∀ P : SchemeHomOver t E'.f, (σ P).1 = P.1 ≫ g := fun P => rfl
  have hmul : ∀ P Q : SchemeHomOver t E'.f, σ (E'.L.mul t P Q) = E.L.mul _ (σ P) (σ Q) := by
    intro P Q
    apply Subtype.ext
    exact hg_mul t P Q
  have hone : σ (E'.L.one t) = E.L.one _ := by
    apply ChartPtsBody.eq_one_of_mul_self
    rw [← hmul, E'.L.one_mul]
  have hinv : ∀ P : SchemeHomOver t E'.f, σ (E'.L.inv t P) = E.L.inv _ (σ P) := by
    intro P
    apply ChartPtsBody.eq_inv_of_mul_eq_one
    rw [← hmul, E'.L.inv_mul_cancel, hone]
  have hns : ∀ (n : ℕ) (P : SchemeHomOver t E'.f), σ (nsmulPt E'.L t n P) = nsmulPt E.L _ n (σ P) := by
    intro n P
    induction n with
    | zero => exact hone
    | succ n ih =>
      show σ (E'.L.mul t (nsmulPt E'.L t n P) P) = E.L.mul _ (nsmulPt E.L _ n (σ P)) (σ P)
      rw [hmul, ih]
  have hact : ∀ (x : ↥Λ) (P : SchemeHomOver t E'.f),
      σ (pushPt (E'.act x) (E'.act_over x) P) = pushPt (E.act x) (E.act_over x) (σ P) := by
    intro x P
    apply Subtype.ext
    change (P.1 ≫ E'.act x) ≫ g = (P.1 ≫ g) ≫ E.act x
    rw [Category.assoc, hg_act, Category.assoc]
  exact ⟨σ, hσ, hone, hmul, hinv, hns, hact⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_equiv_schemeHomOver_of_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_equiv_schemeHomOver_of_isPullback (solution)
