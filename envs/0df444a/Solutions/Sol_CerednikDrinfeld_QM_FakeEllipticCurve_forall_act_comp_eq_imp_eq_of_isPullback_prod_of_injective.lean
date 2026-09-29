-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.forall_act_comp_eq_imp_eq_of_isPullback_prod_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/07e33c71-a032-5d8e-858b-abd4af89b1ec

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_act_comp_eq_imp_eq_of_isPullback_prod_of_injective

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem solution
    {N : ℕ} (S : Type) [CommRing S]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (A₀ : FakeEllipticCurve Λ N S)

    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))

    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (p₁ p₂ : A₀.A ⟶ A) (hp₁ : p₁ ≫ f = A₀.f) (hp₂ : p₂ ≫ f = A₀.f) (hpb : CategoryTheory.IsPullback p₁ p₂ f f)
    (hp_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A₀.f),
      mapPt p₁ hp₁ (A₀.L.mul t P Q) = L.mul t (mapPt p₁ hp₁ P) (mapPt p₁ hp₁ Q) ∧
      mapPt p₂ hp₂ (A₀.L.mul t P Q) = L.mul t (mapPt p₂ hp₂ P) (mapPt p₂ hp₂ Q))
    (E : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ i l, y i l ∈ O) → (A₀.A ⟶ A₀.A))
    (hE : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O), E y hy ≫ A₀.f = A₀.f)
    (hE_mat : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
        {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A₀.f),
      mapPt p₁ hp₁ (pushPt (E y hy) (hE y hy) P) =
        L.mul t (pushPt (ε ⟨y 0 0, hy 0 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 0 1, hy 0 1⟩) (hε _) (mapPt p₂ hp₂ P)) ∧
      mapPt p₂ hp₂ (pushPt (E y hy) (hE y hy) P) =
        L.mul t (pushPt (ε ⟨y 1 0, hy 1 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 1 1, hy 1 1⟩) (hε _) (mapPt p₂ hp₂ P)))
    (hact : ∀ m : ↥Λ, A₀.act m = E (j (m : ℍ[ℚ, a, b])) (hj m))
    (hE_hom : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
        {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A₀.f),
      pushPt (E y hy) (hE y hy) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y hy) (hE y hy) Q))
    (hE_one : ∀ h1 : ∀ i l, (1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) i l ∈ O, E 1 h1 = 𝟙 A₀.A)
    (hE_mul : ∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
        (hyy' : ∀ i l, (y * y') i l ∈ O), E (y * y') hyy' = E y' hy' ≫ E y hy)
    (hE_add : ∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
        (hyy' : ∀ i l, (y + y') i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A₀.f),
      pushPt (E (y + y') hyy') (hE _ hyy') P = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y' hy') (hE y' hy') P))

    {a₁ b₁ : ℚ} (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (hτj : ∀ (x : ℍ[ℚ, a₁, b₁]) (m : ℍ[ℚ, a, b]), τ x * j m = j m * τ x)
    (hε_inj : Function.Injective ε)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O) :
    ∀ x y : ↥R, E (τ (x : ℍ[ℚ, a₁, b₁])) ((hRiff _).1 x.2) = E (τ (y : ℍ[ℚ, a₁, b₁])) ((hRiff _).1 y.2) → x = y := by
  intro x y hxy

  have hε1 : ∀ (z : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)), pushPt (ε z) (hε z) (L.one t) = L.one t := by
    intro z T t
    letI := L.pointGroup t
    have h := hε_hom z t (L.one t) (L.one t)
    rw [L.one_mul] at h
    have h' : (pushPt (ε z) (hε z) (L.one t) : SchemeHomOver t f) = pushPt (ε z) (hε z) (L.one t) * pushPt (ε z) (hε z) (L.one t) := h
    exact mul_eq_left.mp h'.symm

  have key : ∀ (i l : Fin 2), ε ⟨τ (x : ℍ[ℚ, a₁, b₁]) i l, (hRiff _).1 x.2 i l⟩ = ε ⟨τ (y : ℍ[ℚ, a₁, b₁]) i l, (hRiff _).1 y.2 i l⟩ := by
    intro i l

    let Q : SchemeHomOver f f := ⟨𝟙 A, Category.id_comp f⟩
    let e : SchemeHomOver f f := L.one f

    let u : A ⟶ A := if l = 0 then Q.1 else e.1
    let v : A ⟶ A := if l = 0 then e.1 else Q.1
    have hu : u ≫ f = f := by dsimp only [u]; split_ifs; exacts [Q.2, e.2]
    have hv : v ≫ f = f := by dsimp only [v]; split_ifs; exacts [e.2, Q.2]
    let P : SchemeHomOver f A₀.f := ⟨hpb.lift u v (hu.trans hv.symm), by
      rw [← hp₁, ← Category.assoc, hpb.lift_fst]; exact hu⟩
    have hP1 : mapPt p₁ hp₁ P = ⟨u, hu⟩ := by apply Subtype.ext; rw [mapPt_coe]; exact hpb.lift_fst _ _ _
    have hP2 : mapPt p₂ hp₂ P = ⟨v, hv⟩ := by apply Subtype.ext; rw [mapPt_coe]; exact hpb.lift_snd _ _ _

    have hEP : pushPt (E (τ (x : ℍ[ℚ, a₁, b₁])) ((hRiff _).1 x.2)) (hE _ _) P =
        pushPt (E (τ (y : ℍ[ℚ, a₁, b₁])) ((hRiff _).1 y.2)) (hE _ _) P := by
      apply Subtype.ext; rw [mapPt_coe, mapPt_coe, hxy]
    have hx := hE_mat (τ (x : ℍ[ℚ, a₁, b₁])) ((hRiff _).1 x.2) f P
    have hy := hE_mat (τ (y : ℍ[ℚ, a₁, b₁])) ((hRiff _).1 y.2) f P
    rw [hP1, hP2] at hx hy
    rw [hEP] at hx

    letI := L.pointGroup f
    have row : ∀ (z z' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hz : ∀ i l, z i l ∈ O) (hz' : ∀ i l, z' i l ∈ O),
        L.mul f (pushPt (ε ⟨z i 0, hz i 0⟩) (hε _) ⟨u, hu⟩) (pushPt (ε ⟨z i 1, hz i 1⟩) (hε _) ⟨v, hv⟩) =
          L.mul f (pushPt (ε ⟨z' i 0, hz' i 0⟩) (hε _) ⟨u, hu⟩) (pushPt (ε ⟨z' i 1, hz' i 1⟩) (hε _) ⟨v, hv⟩) →
        ε ⟨z i l, hz i l⟩ = ε ⟨z' i l, hz' i l⟩ := by
      intro z z' hz hz' h
      fin_cases l
      ·
        have hv0 : (⟨v, hv⟩ : SchemeHomOver f f) = L.one f := by apply Subtype.ext; simp [v, e]
        have hu0 : (⟨u, hu⟩ : SchemeHomOver f f) = Q := by apply Subtype.ext; simp [u, Q]
        rw [hv0, hu0, hε1, hε1, L.mul_one, L.mul_one] at h
        have := congrArg Subtype.val h
        rw [mapPt_coe, mapPt_coe] at this
        simpa [Q] using this
      ·
        have hu0 : (⟨u, hu⟩ : SchemeHomOver f f) = L.one f := by apply Subtype.ext; simp [u, e]
        have hv0 : (⟨v, hv⟩ : SchemeHomOver f f) = Q := by apply Subtype.ext; simp [v, Q]
        rw [hv0, hu0, hε1, hε1, L.one_mul, L.one_mul] at h
        have := congrArg Subtype.val h
        rw [mapPt_coe, mapPt_coe] at this
        simpa [Q] using this
    fin_cases i
    · exact row _ _ _ _ (hx.1.symm.trans hy.1)
    · exact row _ _ _ _ (hx.2.symm.trans hy.2)

  apply Subtype.ext
  apply hτ
  funext i l
  have := hε_inj (key i l)
  exact congrArg Subtype.val this

end S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_act_comp_eq_imp_eq_of_isPullback_prod_of_injective
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_act_comp_eq_imp_eq_of_isPullback_prod_of_injective (solution)
