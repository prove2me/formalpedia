-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/83bba9c6-6396-538e-a804-23167fdd2db1

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_AlgebraicGeometry_exists_intermediateField_forall_exists_hom_comp_eq_of_isPullback_of_isAlgebraic
import Theorems.Thm_AlgebraicGeometry_surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace ActSpread9

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

theorem one_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) :
    (L.one t₁).1 = (L.one t₂).1 := by
  subst h; rfl

theorem inv_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (P₁ : SchemeHomOver t₁ f) (P₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) :
    (L.inv t₁ P₁).1 = (L.inv t₂ P₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  rfl

theorem inv_natural {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t'
  have h : GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) * GoodReductionJacobian.schemeHomOverComp ψ hψ x = 1 := by
    show G.mul t' _ _ = G.one t'
    rw [← G.mul_natural t t' ψ hψ, G.inv_mul_cancel, G.one_natural]
  exact eq_inv_of_mul_eq_one_left h

section Setup

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
variable {K : Type} [Field K] {S : Type} [Field S] [Algebra S K]
variable (E : FakeEllipticCurve Λ N K)
variable {X₂ : Scheme.{0}} (f₂ : X₂ ⟶ Spec (CommRingCat.of S))
variable (r : E.A ⟶ X₂) (hr : CategoryTheory.IsPullback r E.f f₂ (Spec.map (CommRingCat.ofHom (algebraMap S K))))
variable (L₂ : RelativeGroupLaw S f₂)

include hr in
theorem epi_r : Epi r := by
  obtain ⟨h1, h2, h3⟩ := AlgebraicGeometry.surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field r hr
  haveI := h1; haveI := h2; haveI := h3
  infer_instance

def ρ {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of K)} (P : SchemeHomOver t' E.f) :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S K))) f₂ :=
  ⟨P.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem ρ_coe {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of K)} (P : SchemeHomOver t' E.f) :
    (ρ E f₂ r hr P).1 = P.1 ≫ r := rfl

def MulCompat : Prop :=
  ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' E.f),
    (E.L.mul t' P Q).1 ≫ r =
      (L₂.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S K)))
        ⟨P.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, Q.2]⟩).1

variable {E f₂ r hr L₂}

theorem ρ_mul (hm : MulCompat E f₂ r hr L₂) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' E.f) :
    ρ E f₂ r hr (E.L.mul t' P Q) = L₂.mul _ (ρ E f₂ r hr P) (ρ E f₂ r hr Q) :=
  Subtype.ext (hm t' P Q)

theorem ρ_one (hm : MulCompat E f₂ r hr L₂) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) :
    ρ E f₂ r hr (E.L.one t') = L₂.one _ := by
  letI := E.L.pointGroup t'
  letI := L₂.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S K)))
  let h : SchemeHomOver t' E.f →* SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S K))) f₂ :=
    MonoidHom.mk' (ρ E f₂ r hr) (ρ_mul hm t')
  exact map_one h

theorem ρ_inv (hm : MulCompat E f₂ r hr L₂) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t' E.f) :
    ρ E f₂ r hr (E.L.inv t' P) = L₂.inv _ (ρ E f₂ r hr P) := by
  letI := E.L.pointGroup t'
  letI := L₂.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S K)))
  let h : SchemeHomOver t' E.f →* SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S K))) f₂ :=
    MonoidHom.mk' (ρ E f₂ r hr) (ρ_mul hm t')
  exact map_inv h P

variable (E) in

def idPt : SchemeHomOver E.f E.f := ⟨𝟙 E.A, Category.id_comp _⟩

variable (E) in

def actPt (x : ↥Λ) : SchemeHomOver E.f E.f := pushPt (E.act x) (E.act_over x) (idPt E)

@[scoped simp] theorem actPt_coe (x : ↥Λ) : (actPt E x).1 = E.act x := Category.id_comp _

theorem actPt_add (x y : ↥Λ) : actPt E (x + y) = E.L.mul E.f (actPt E x) (actPt E y) :=
  E.act_add x y E.f (idPt E)

theorem actPt_zero : actPt E 0 = E.L.one E.f := by
  letI := E.L.pointGroup E.f
  have h : actPt E 0 * actPt E 0 = actPt E 0 := by
    show E.L.mul E.f _ _ = _
    rw [← actPt_add, add_zero]
  exact mul_eq_left.mp h

theorem actPt_neg (x : ↥Λ) : actPt E (-x) = E.L.inv E.f (actPt E x) := by
  letI := E.L.pointGroup E.f
  have h : actPt E x * actPt E (-x) = 1 := by
    show E.L.mul E.f _ _ = E.L.one E.f
    rw [← actPt_add, add_neg_cancel, actPt_zero]
  exact (eq_inv_of_mul_eq_one_right h)

variable (E r) in

def Desc (x : ↥Λ) (φ₂ : X₂ ⟶ X₂) : Prop := E.act x ≫ r = r ≫ φ₂

include f₂ hr in
theorem desc_over {x : ↥Λ} {φ₂ : X₂ ⟶ X₂} (h : Desc E r x φ₂) : φ₂ ≫ f₂ = f₂ := by
  haveI := epi_r E f₂ r hr
  rw [← cancel_epi r, ← Category.assoc, ← h, Category.assoc, hr.w, ← Category.assoc, E.act_over]

include f₂ hr in
theorem desc_unique {x : ↥Λ} {φ₂ ψ₂ : X₂ ⟶ X₂} (h : Desc E r x φ₂) (h' : Desc E r x ψ₂) : φ₂ = ψ₂ := by
  haveI := epi_r E f₂ r hr
  rw [← cancel_epi r, ← h, h']

theorem desc_zero (hm : MulCompat E f₂ r hr L₂) : Desc E r 0 (L₂.one f₂).1 := by
  show E.act 0 ≫ r = r ≫ (L₂.one f₂).1
  have h1 : E.act 0 ≫ r = (ρ E f₂ r hr (actPt E 0)).1 := by rw [ρ_coe, actPt_coe]
  rw [h1, actPt_zero, ρ_one hm]
  have h2 := congrArg Subtype.val (L₂.one_natural f₂ _ r hr.w)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h2
  rw [h2]

theorem desc_add (hm : MulCompat E f₂ r hr L₂) {x y : ↥Λ} {φ ψ : X₂ ⟶ X₂} (hφ : Desc E r x φ) (hψ : Desc E r y ψ) :
    Desc E r (x + y) (L₂.mul f₂ ⟨φ, desc_over (f₂ := f₂) (hr := hr) hφ⟩ ⟨ψ, desc_over (f₂ := f₂) (hr := hr) hψ⟩).1 := by
  show E.act (x + y) ≫ r = r ≫ _
  have h1 : E.act (x + y) ≫ r = (ρ E f₂ r hr (actPt E (x + y))).1 := by rw [ρ_coe, actPt_coe]
  rw [h1, actPt_add, ρ_mul hm]
  have h2 := congrArg Subtype.val (L₂.mul_natural f₂ _ r hr.w ⟨φ, desc_over (f₂ := f₂) (hr := hr) hφ⟩ ⟨ψ, desc_over (f₂ := f₂) (hr := hr) hψ⟩)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h2
  rw [h2]
  apply mul_val_congr L₂ rfl
  · rw [ρ_coe, actPt_coe, GoodReductionJacobian.schemeHomOverComp_coe]; exact hφ
  · rw [ρ_coe, actPt_coe, GoodReductionJacobian.schemeHomOverComp_coe]; exact hψ

theorem desc_neg (hm : MulCompat E f₂ r hr L₂) {x : ↥Λ} {φ : X₂ ⟶ X₂} (hφ : Desc E r x φ) :
    Desc E r (-x) (L₂.inv f₂ ⟨φ, desc_over (f₂ := f₂) (hr := hr) hφ⟩).1 := by
  show E.act (-x) ≫ r = r ≫ _
  have h1 : E.act (-x) ≫ r = (ρ E f₂ r hr (actPt E (-x))).1 := by rw [ρ_coe, actPt_coe]
  rw [h1, actPt_neg, ρ_inv hm]
  have h2 := congrArg Subtype.val (inv_natural L₂ f₂ _ r hr.w ⟨φ, desc_over (f₂ := f₂) (hr := hr) hφ⟩)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h2
  rw [h2]
  apply inv_val_congr L₂ rfl
  rw [ρ_coe, actPt_coe, GoodReductionJacobian.schemeHomOverComp_coe]; exact hφ

end Setup

section Descent

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
variable {K : Type} [Field K] {S : Type} [Field S] [Algebra S K]
variable {E : FakeEllipticCurve Λ N K}
variable {X₂ : Scheme.{0}} {f₂ : X₂ ⟶ Spec (CommRingCat.of S)}
variable {r : E.A ⟶ X₂} {hr : CategoryTheory.IsPullback r E.f f₂ (Spec.map (CommRingCat.ofHom (algebraMap S K)))}
variable {L₂ : RelativeGroupLaw S f₂}

theorem pushPt_coe {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A) (hφ : φ ≫ f = f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) : (pushPt φ hφ P).1 = P.1 ≫ φ := rfl

theorem hom_descend (hm : MulCompat E f₂ r hr L₂) {x : ↥Λ} {φ₂ : X₂ ⟶ X₂} (hφ : Desc E r x φ₂) (hφ₂ : φ₂ ≫ f₂ = f₂)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f₂) :
    pushPt φ₂ hφ₂ (L₂.mul t P Q) = L₂.mul t (pushPt φ₂ hφ₂ P) (pushPt φ₂ hφ₂ Q) := by
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap S K))) := inferInstance
  haveI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap S K))) := inferInstance
  haveI : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap S K))) := inferInstance
  apply Subtype.ext
  let pr : pullback t (Spec.map (CommRingCat.ofHom (algebraMap S K))) ⟶ T := pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap S K)))
  let t' : pullback t (Spec.map (CommRingCat.ofHom (algebraMap S K))) ⟶ Spec (CommRingCat.of K) := pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap S K)))
  have hpr : pr ≫ t = t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S K)) := pullback.condition
  haveI : Epi pr := by show Epi (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap S K)))); infer_instance
  rw [← cancel_epi pr]
  have liftE : ∀ R : SchemeHomOver t f₂, ∃ R' : SchemeHomOver t' E.f, R'.1 ≫ r = pr ≫ R.1 := by
    intro R
    refine ⟨⟨hr.lift (pr ≫ R.1) t' (by rw [Category.assoc, R.2, hpr]), hr.lift_snd _ _ _⟩, hr.lift_fst _ _ _⟩
  obtain ⟨P', hP'⟩ := liftE P
  obtain ⟨Q', hQ'⟩ := liftE Q
  have natA : pr ≫ (L₂.mul t P Q).1 =
      (L₂.mul (pr ≫ t) (GoodReductionJacobian.schemeHomOverComp pr rfl P) (GoodReductionJacobian.schemeHomOverComp pr rfl Q)).1 :=
    congrArg Subtype.val (L₂.mul_natural t (pr ≫ t) pr rfl P Q)
  have natD : pr ≫ (L₂.mul t (pushPt φ₂ hφ₂ P) (pushPt φ₂ hφ₂ Q)).1 =
      (L₂.mul (pr ≫ t) (GoodReductionJacobian.schemeHomOverComp pr rfl (pushPt φ₂ hφ₂ P))
        (GoodReductionJacobian.schemeHomOverComp pr rfl (pushPt φ₂ hφ₂ Q))).1 :=
    congrArg Subtype.val (L₂.mul_natural t (pr ≫ t) pr rfl (pushPt φ₂ hφ₂ P) (pushPt φ₂ hφ₂ Q))
  have key : ∀ (u : pullback t (Spec.map (CommRingCat.ofHom (algebraMap S K))) ⟶ Spec (CommRingCat.of S))
      (hu : u = t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S K)))
      (A B : SchemeHomOver u f₂) (hA : A.1 = P'.1 ≫ r) (hB : B.1 = Q'.1 ≫ r),
      (L₂.mul u A B).1 ≫ φ₂ =
        (L₂.mul u ⟨A.1 ≫ φ₂, by rw [Category.assoc, hφ₂, A.2]⟩ ⟨B.1 ≫ φ₂, by rw [Category.assoc, hφ₂, B.2]⟩).1 := by
    intro u hu A B hA hB
    subst hu
    obtain ⟨A1, A2⟩ := A; obtain ⟨B1, B2⟩ := B
    simp only at hA hB
    subst hA; subst hB
    have hφ' : r ≫ φ₂ = E.act x ≫ r := hφ.symm
    rw [← hm t' P' Q', Category.assoc, hφ', ← Category.assoc,
      show (E.L.mul t' P' Q').1 ≫ E.act x = (pushPt (E.act x) (E.act_over x) (E.L.mul t' P' Q')).1 from rfl,
      E.act_hom x t' P' Q', hm]
    congr 2 <;> (apply Subtype.ext; simp only [pushPt_coe, Category.assoc, hφ'])
  have h1 : (GoodReductionJacobian.schemeHomOverComp pr rfl P).1 = P'.1 ≫ r := by
    rw [GoodReductionJacobian.schemeHomOverComp_coe, hP']
  have h2 : (GoodReductionJacobian.schemeHomOverComp pr rfl Q).1 = Q'.1 ≫ r := by
    rw [GoodReductionJacobian.schemeHomOverComp_coe, hQ']
  rw [pushPt_coe, ← Category.assoc, natA, natD, key (pr ≫ t) hpr _ _ h1 h2]
  congr 1 <;> (apply Subtype.ext; simp only [GoodReductionJacobian.schemeHomOverComp_coe, pushPt_coe, Category.assoc])

end Descent

end ActSpread9
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg.ActSpread9"

open ActSpread9 in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : Λ.FG) {N : ℕ}
    (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (L : IntermediateField k K) [FiniteDimensional k ↥L]
    (E : FakeEllipticCurve Λ N K)
    {X₀ : Scheme.{0}} (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥L)) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFiniteType f₀]
    (g : E.A ⟶ X₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥L K)))) :
    ∃ (Lι : IntermediateField k K) (_ : FiniteDimensional k ↥Lι) (_ : L ≤ Lι),
      ∀ (L'' : IntermediateField k K) (_ : Lι ≤ L'')
        (j : ↥L →+* ↥L'') (_ : ∀ x : ↥L, ((j x : ↥L'') : K) = (x : K))
        (X₂ : Scheme.{0}) (f₂ : X₂ ⟶ Spec (CommRingCat.of ↥L''))
        (r : E.A ⟶ X₂) (hr : CategoryTheory.IsPullback r E.f f₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))))
        (q : X₂ ⟶ X₀) (_ : CategoryTheory.IsPullback q f₂ f₀ (Spec.map (CommRingCat.ofHom j))) (_ : r ≫ q = g)
        (L₂ : RelativeGroupLaw ↥L'' f₂)
        (_ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' E.f),
          (E.L.mul t' P Q).1 ≫ r =
            (L₂.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K)))
              ⟨P.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, Q.2]⟩).1),
        ∃ (act₂ : ↥Λ → (X₂ ⟶ X₂)) (hact₂ : ∀ x : ↥Λ, act₂ x ≫ f₂ = f₂),
          (∀ x : ↥Λ, E.act x ≫ r = r ≫ act₂ x) ∧
          (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥L'')) (P Q : SchemeHomOver t f₂),
            pushPt (act₂ x) (hact₂ x) (L₂.mul t P Q) =
              L₂.mul t (pushPt (act₂ x) (hact₂ x) P) (pushPt (act₂ x) (hact₂ x) Q)) ∧
          (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act₂ ⟨1, h⟩ = 𝟙 X₂) ∧
          (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
            act₂ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act₂ y ≫ act₂ x) ∧
          (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥L'')) (P : SchemeHomOver t f₂),
            pushPt (act₂ (x + y)) (hact₂ (x + y)) P =
              L₂.mul t (pushPt (act₂ x) (hact₂ x) P) (pushPt (act₂ y) (hact₂ y) P)) := by
  classical
  haveI : CompactSpace ↥X₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  haveI : QuasiSeparatedSpace ↥X₀ := quasiSeparatedSpace_of_quasiSeparated f₀
  obtain ⟨Sgen, hSfin, hspan⟩ := Submodule.fg_def.mp hΛ
  haveI : Finite ↥Sgen := hSfin.to_subtype
  have memΛ : ∀ {y : ℍ[ℚ, a, b]}, y ∈ AddSubgroup.closure Sgen → y ∈ Λ := by
    intro y hy
    rw [← Submodule.span_int_eq_addSubgroupClosure, hspan] at hy
    exact hy

  have hgen : ∀ s : ↥Sgen, ∃ (Ls : IntermediateField k K) (_ : FiniteDimensional k ↥Ls) (_ : L ≤ Ls),
      ∀ (L'' : IntermediateField k K) (_ : Ls ≤ L'')
        (j : ↥L →+* ↥L'') (_ : ∀ x : ↥L, ((j x : ↥L'') : K) = (x : K))
        (X₂ Y₂ : Scheme.{0}) (fX₂ : X₂ ⟶ Spec (CommRingCat.of ↥L'')) (fY₂ : Y₂ ⟶ Spec (CommRingCat.of ↥L''))
        (rX : E.A ⟶ X₂) (_ : IsPullback rX E.f fX₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))))
        (qX : X₂ ⟶ X₀) (_ : IsPullback qX fX₂ f₀ (Spec.map (CommRingCat.ofHom j))) (_ : rX ≫ qX = g)
        (rY : E.A ⟶ Y₂) (_ : IsPullback rY E.f fY₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))))
        (qY : Y₂ ⟶ X₀) (_ : IsPullback qY fY₂ f₀ (Spec.map (CommRingCat.ofHom j))) (_ : rY ≫ qY = g),
        ∃ φ₂ : X₂ ⟶ Y₂, φ₂ ≫ fY₂ = fX₂ ∧ rX ≫ φ₂ = E.act ⟨s.1, memΛ (AddSubgroup.subset_closure s.2)⟩ ≫ rY := by
    intro s
    exact AlgebraicGeometry.exists_intermediateField_forall_exists_hom_comp_eq_of_isPullback_of_isAlgebraic k K L
      E.f E.f f₀ f₀ g hg g hg (E.act _) (E.act_over _)
  choose Ls hLsfin hLLs hLs using hgen
  haveI : ∀ s, FiniteDimensional k ↥(Ls s) := hLsfin
  refine ⟨L ⊔ ⨆ s, Ls s, inferInstance, le_sup_left, ?_⟩
  intro L'' hL'' j hj X₂ f₂ r hr q hq hrq L₂ hmul
  have hm : MulCompat E f₂ r hr L₂ := fun t' P Q => hmul t' P Q

  have hgenD : ∀ s : ↥Sgen, ∃ φ₂ : X₂ ⟶ X₂, Desc E r ⟨s.1, memΛ (AddSubgroup.subset_closure s.2)⟩ φ₂ := by
    intro s
    have hle : Ls s ≤ L'' := le_trans (le_trans (le_iSup (fun s => Ls s) s) le_sup_right) hL''
    obtain ⟨φ₂, -, hcomm⟩ := hLs s L'' hle j hj X₂ X₂ f₂ f₂ r hr q hq hrq r hr q hq hrq
    exact ⟨φ₂, hcomm.symm⟩

  have hall : ∀ x : ↥Λ, ∃ φ₂ : X₂ ⟶ X₂, Desc E r x φ₂ := by
    intro x
    have hx : (x : ℍ[ℚ, a, b]) ∈ AddSubgroup.closure Sgen := by
      have h : (x : ℍ[ℚ, a, b]) ∈ Submodule.span ℤ Sgen := by rw [hspan]; exact x.2
      rw [← Submodule.span_int_eq_addSubgroupClosure]
      exact h
    refine AddSubgroup.closure_induction
      (p := fun y _ => ∀ hy' : y ∈ Λ, ∃ φ₂ : X₂ ⟶ X₂, Desc E r ⟨y, hy'⟩ φ₂) ?_ ?_ ?_ ?_ hx x.2
    · intro y hy hy'
      exact hgenD ⟨y, hy⟩
    · intro hy'
      exact ⟨_, desc_zero (hr := hr) hm⟩
    · intro y z hy hz ihy ihz hyz'
      obtain ⟨φ, hφ⟩ := ihy (memΛ hy)
      obtain ⟨ψ, hψ⟩ := ihz (memΛ hz)
      exact ⟨_, desc_add (hr := hr) hm hφ hψ⟩
    · intro y hy ih hy'
      obtain ⟨φ, hφ⟩ := ih (memΛ hy)
      exact ⟨_, desc_neg (hr := hr) hm hφ⟩
  choose act₂ hact₂ using hall
  haveI : Epi r := epi_r E f₂ r hr
  have hover : ∀ x : ↥Λ, act₂ x ≫ f₂ = f₂ := fun x => desc_over (f₂ := f₂) (hr := hr) (hact₂ x)
  refine ⟨act₂, hover, fun x => hact₂ x, ?_, ?_, ?_, ?_⟩
  · intro x T t P Q
    exact hom_descend (hr := hr) hm (hact₂ x) (hover x) t P Q
  · intro h1
    rw [← cancel_epi r, ← hact₂ ⟨1, h1⟩, E.act_one h1, Category.id_comp, Category.comp_id]
  · intro x y hxy
    rw [← cancel_epi r]
    calc r ≫ act₂ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ ≫ r :=
          (hact₂ _).symm
      _ = (E.act y ≫ E.act x) ≫ r := by rw [E.act_mul x y hxy]
      _ = r ≫ act₂ y ≫ act₂ x := by rw [Category.assoc, hact₂ x, ← Category.assoc, hact₂ y, Category.assoc]
  · intro x y T t P
    have e : act₂ (x + y) = (L₂.mul f₂ ⟨act₂ x, hover x⟩ ⟨act₂ y, hover y⟩).1 :=
      desc_unique (f₂ := f₂) (hr := hr) (hact₂ (x + y)) (desc_add (hr := hr) hm (hact₂ x) (hact₂ y))
    apply Subtype.ext
    rw [pushPt_coe, e]
    have h := congrArg Subtype.val (L₂.mul_natural f₂ t P.1 P.2 ⟨act₂ x, hover x⟩ ⟨act₂ y, hover y⟩)
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
    rw [h]
    exact mul_val_congr L₂ rfl _ _ _ _ rfl rfl

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg (solution)
