-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/753d49ad-49fb-5704-912d-3389947d2c90

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_AlgebraicGeometry_exists_section_comp_eq_of_finite_flat_valuationSubring
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_isTorsionPoint_of_comp_residue_eq
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_valuationSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve"
open scoped Quaternion

namespace FibreConstAux

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

theorem one_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) :
    (L.one t₁).1 = (L.one t₂).1 := by
  subst h; rfl

theorem exists_ringHom_comp_subtype_eq {k : Type} [Field k] (O : ValuationSubring (AlgebraicClosure ℚ))
    (sk : ↥O →+* k) (hinj : Function.Injective sk) :
    ∃ j : AlgebraicClosure ℚ →+* k, j.comp O.subtype = sk := by
  have hunit : ∀ y : ↥(nonZeroDivisors ↥O), IsUnit (sk (y : ↥O)) := fun y =>
    isUnit_iff_ne_zero.mpr (fun h0 => nonZeroDivisors.ne_zero y.2 (hinj (by rw [h0, map_zero])))
  refine ⟨IsLocalization.lift (M := nonZeroDivisors ↥O) (S := AlgebraicClosure ℚ) hunit, ?_⟩
  ext x
  exact IsLocalization.lift_eq (M := nonZeroDivisors ↥O) hunit x

end FibreConstAux

theorem caseZero
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ)
    (𝒜 : FakeEllipticCurve Λ N ↥O) (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (K : E.ExtraLevel ℓ)
    {Kk : Scheme.{0}} (ι : Kk ⟶ 𝒜.A) [IsClosedImmersion ι]
    [IsFinite (ι ≫ 𝒜.f)] [Flat (ι ≫ 𝒜.f)] [LocallyOfFinitePresentation (ι ≫ 𝒜.f)]
    (hrank : ∀ s : ↥(Spec (CommRingCat.of ↥O)), (ι ≫ 𝒜.f).finrank s = ℓ ^ 2)
    (hsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → FactorsThrough ι Q →
        FactorsThrough ι (𝒜.L.mul t P Q) ∧ FactorsThrough ι (𝒜.L.inv t P))
    (hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)), FactorsThrough ι (𝒜.L.one t))
    (htors : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → nsmulPt 𝒜.L t ℓ P = 𝒜.L.one t)
    (hgen : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t' E.f),
      FactorsThrough K.levK P ↔ ∃ P₀ : T ⟶ Kk, P₀ ≫ ι = P.1 ≫ gE)
    (k : Type) [Field k] [IsAlgClosed k] (sk : ↥O →+* k) (hℓ : (ℓ : k) ≠ 0)
    (hinj : Function.Injective sk) :
      ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (geomPoint k sk) 𝒜.f // FactorsThrough ι P},
        ∀ x y : ZMod ℓ × ZMod ℓ, (e (x + y) : SchemeHomOver (geomPoint k sk) 𝒜.f) =
          𝒜.L.mul (geomPoint k sk) (e x) (e y) := by
  classical
  obtain ⟨j, hj⟩ := FibreConstAux.exists_ringHom_comp_subtype_eq O sk hinj
  subst hj

  have ht : geomPoint k j ≫ Spec.map (CommRingCat.ofHom O.subtype) = geomPoint k (j.comp O.subtype) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

  obtain ⟨eK, heK⟩ := K.levK_fibre k j hℓ

  have fwd_over : ∀ Q : SchemeHomOver (geomPoint k j) E.f,
      (Q.1 ≫ gE) ≫ 𝒜.f = geomPoint k (j.comp O.subtype) := fun Q => by
    rw [Category.assoc, hgE.w, ← Category.assoc, Q.2, ht]
  have bwd_w : ∀ P : SchemeHomOver (geomPoint k (j.comp O.subtype)) 𝒜.f,
      P.1 ≫ 𝒜.f = geomPoint k j ≫ Spec.map (CommRingCat.ofHom O.subtype) := fun P => by
    rw [P.2, ht]
  let Φ : {Q : SchemeHomOver (geomPoint k j) E.f // FactorsThrough K.levK Q} ≃
      {P : SchemeHomOver (geomPoint k (j.comp O.subtype)) 𝒜.f // FactorsThrough ι P} :=
    { toFun := fun Q => ⟨⟨Q.1.1 ≫ gE, fwd_over Q.1⟩, (hgen _ Q.1).mp Q.2⟩
      invFun := fun P => ⟨⟨hgE.lift P.1.1 (geomPoint k j) (bwd_w P.1), hgE.lift_snd _ _ _⟩,
        (hgen _ _).mpr (by obtain ⟨P₀, hP₀⟩ := P.2; exact ⟨P₀, by rw [hP₀, hgE.lift_fst]⟩)⟩
      left_inv := fun Q => by
        apply Subtype.ext; apply Subtype.ext
        apply hgE.hom_ext
        · rw [hgE.lift_fst]
        · rw [hgE.lift_snd]; exact Q.1.2.symm
      right_inv := fun P => by
        apply Subtype.ext; apply Subtype.ext
        exact hgE.lift_fst _ _ _ }
  refine ⟨eK.trans Φ, fun x y => ?_⟩
  apply Subtype.ext
  show ((eK (x + y) : SchemeHomOver (geomPoint k j) E.f).1 ≫ gE) =
    (𝒜.L.mul (geomPoint k (j.comp O.subtype)) (Φ (eK x)).1 (Φ (eK y)).1).1
  rw [heK x y, hgE_mul]
  exact FibreConstAux.mul_val_congr 𝒜.L ht _ _ _ _ rfl rfl

namespace CasePAux

variable {R : Type} [CommRing R] {A C : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem factorsThrough_comp (lev : C ⟶ A) {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P : SchemeHomOver t f)
    (hP : FactorsThrough lev P) : FactorsThrough lev (GoodReductionJacobian.schemeHomOverComp ψ hψ P) := by
  obtain ⟨P₀, hP₀⟩ := hP
  exact ⟨ψ ≫ P₀, by rw [Category.assoc, hP₀]; rfl⟩

noncomputable def compK (lev : C ⟶ A) {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    {P : SchemeHomOver t f // FactorsThrough lev P} → {P : SchemeHomOver t' f // FactorsThrough lev P} :=
  fun P => ⟨GoodReductionJacobian.schemeHomOverComp ψ hψ P.1, factorsThrough_comp lev ψ hψ P.1 P.2⟩

@[scoped simp] theorem compK_val (lev : C ⟶ A) {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (P : {P : SchemeHomOver t f // FactorsThrough lev P}) :
    ((compK lev ψ hψ P).1 : SchemeHomOver t' f).1 = ψ ≫ P.1.1 := rfl

theorem exists_equiv_of_bijective (L : GoodReductionJacobian.RelativeGroupLaw R f) (lev : C ⟶ A)
    (hsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev Q → FactorsThrough lev (L.mul t P Q) ∧ FactorsThrough lev (L.inv t P))
    {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (hbij : Function.Bijective (compK (f := f) lev ψ hψ)) :
    ∃ e : {P : SchemeHomOver t f // FactorsThrough lev P} ≃ {P : SchemeHomOver t' f // FactorsThrough lev P},
      ∀ x y : {P : SchemeHomOver t f // FactorsThrough lev P},
        (e ⟨L.mul t x.1 y.1, (hsub t x.1 y.1 x.2 y.2).1⟩ : SchemeHomOver t' f) = L.mul t' (e x) (e y) := by
  refine ⟨Equiv.ofBijective _ hbij, fun x y => ?_⟩
  show GoodReductionJacobian.schemeHomOverComp ψ hψ (L.mul t x.1 y.1) = L.mul t' _ _
  rw [L.mul_natural t t' ψ hψ]
  rfl

theorem exists_equiv_of_eq (L : GoodReductionJacobian.RelativeGroupLaw R f) (lev : C ⟶ A)
    (hsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev Q → FactorsThrough lev (L.mul t P Q) ∧ FactorsThrough lev (L.inv t P))
    {T : Scheme.{0}} (t t' : T ⟶ Spec (CommRingCat.of R)) (h : t = t') :
    ∃ e : {P : SchemeHomOver t f // FactorsThrough lev P} ≃ {P : SchemeHomOver t' f // FactorsThrough lev P},
      ∀ x y : {P : SchemeHomOver t f // FactorsThrough lev P},
        (e ⟨L.mul t x.1 y.1, (hsub t x.1 y.1 x.2 y.2).1⟩ : SchemeHomOver t' f) = L.mul t' (e x) (e y) := by
  subst h; exact ⟨Equiv.refl _, fun x y => rfl⟩

end CasePAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring.CasePAux"

namespace CasePAux

variable {R : Type} [CommRing R] {A C : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

def IsMul (L : GoodReductionJacobian.RelativeGroupLaw R f) (lev : C ⟶ A)
    (hsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev Q → FactorsThrough lev (L.mul t P Q) ∧ FactorsThrough lev (L.inv t P))
    {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (e : {P : SchemeHomOver t f // FactorsThrough lev P} ≃ {P : SchemeHomOver t' f // FactorsThrough lev P}) : Prop :=
  ∀ x y : {P : SchemeHomOver t f // FactorsThrough lev P},
    (e ⟨L.mul t x.1 y.1, (hsub t x.1 y.1 x.2 y.2).1⟩ : SchemeHomOver t' f) = L.mul t' (e x) (e y)

variable (L : GoodReductionJacobian.RelativeGroupLaw R f) (lev : C ⟶ A)
    (hsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev Q → FactorsThrough lev (L.mul t P Q) ∧ FactorsThrough lev (L.inv t P))

theorem IsMul.trans {T₁ T₂ T₃ : Scheme.{0}} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    {t₃ : T₃ ⟶ Spec (CommRingCat.of R)}
    {e₁ : {P : SchemeHomOver t₁ f // FactorsThrough lev P} ≃ {P : SchemeHomOver t₂ f // FactorsThrough lev P}}
    {e₂ : {P : SchemeHomOver t₂ f // FactorsThrough lev P} ≃ {P : SchemeHomOver t₃ f // FactorsThrough lev P}}
    (h₁ : IsMul L lev hsub t₁ t₂ e₁) (h₂ : IsMul L lev hsub t₂ t₃ e₂) : IsMul L lev hsub t₁ t₃ (e₁.trans e₂) := by
  intro x y
  show (e₂ (e₁ ⟨L.mul t₁ x.1 y.1, _⟩) : SchemeHomOver t₃ f) = L.mul t₃ (e₂ (e₁ x)) (e₂ (e₁ y))
  have : e₁ ⟨L.mul t₁ x.1 y.1, (hsub t₁ x.1 y.1 x.2 y.2).1⟩ =
      ⟨L.mul t₂ (e₁ x).1 (e₁ y).1, (hsub t₂ _ _ (e₁ x).2 (e₁ y).2).1⟩ := Subtype.ext (h₁ x y)
  rw [this]
  exact h₂ (e₁ x) (e₁ y)

theorem IsMul.symm {T₁ T₂ : Scheme.{0}} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    {e : {P : SchemeHomOver t₁ f // FactorsThrough lev P} ≃ {P : SchemeHomOver t₂ f // FactorsThrough lev P}}
    (h : IsMul L lev hsub t₁ t₂ e) : IsMul L lev hsub t₂ t₁ e.symm := by
  intro x y
  have key : e ⟨L.mul t₁ (e.symm x).1 (e.symm y).1, (hsub t₁ _ _ (e.symm x).2 (e.symm y).2).1⟩ =
      ⟨L.mul t₂ x.1 y.1, (hsub t₂ x.1 y.1 x.2 y.2).1⟩ := by
    apply Subtype.ext
    rw [h (e.symm x) (e.symm y), Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have := congrArg e.symm key
  rw [Equiv.symm_apply_apply] at this
  exact congrArg Subtype.val this.symm

theorem param_trans {ι₀ : Type} [Add ι₀] {T₁ T₂ : Scheme.{0}} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (e₀ : ι₀ ≃ {P : SchemeHomOver t₁ f // FactorsThrough lev P})
    (h₀ : ∀ x y : ι₀, (e₀ (x + y) : SchemeHomOver t₁ f) = L.mul t₁ (e₀ x) (e₀ y))
    {e : {P : SchemeHomOver t₁ f // FactorsThrough lev P} ≃ {P : SchemeHomOver t₂ f // FactorsThrough lev P}}
    (h : IsMul L lev hsub t₁ t₂ e) :
    ∀ x y : ι₀, ((e₀.trans e) (x + y) : SchemeHomOver t₂ f) = L.mul t₂ ((e₀.trans e) x) ((e₀.trans e) y) := by
  intro x y
  show (e (e₀ (x + y)) : SchemeHomOver t₂ f) = L.mul t₂ (e (e₀ x)) (e (e₀ y))
  have : e₀ (x + y) = ⟨L.mul t₁ (e₀ x).1 (e₀ y).1, (hsub t₁ _ _ (e₀ x).2 (e₀ y).2).1⟩ := Subtype.ext (h₀ x y)
  rw [this]
  exact h (e₀ x) (e₀ y)

theorem isMul_of_bijective {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (hbij : Function.Bijective (compK (f := f) lev ψ hψ)) :
    ∃ e : {P : SchemeHomOver t f // FactorsThrough lev P} ≃ {P : SchemeHomOver t' f // FactorsThrough lev P},
      IsMul L lev hsub t t' e :=
  exists_equiv_of_bijective L lev hsub t t' ψ hψ hbij

theorem isMul_of_eq {T : Scheme.{0}} (t t' : T ⟶ Spec (CommRingCat.of R)) (h : t = t') :
    ∃ e : {P : SchemeHomOver t f // FactorsThrough lev P} ≃ {P : SchemeHomOver t' f // FactorsThrough lev P},
      IsMul L lev hsub t t' e :=
  exists_equiv_of_eq L lev hsub t t' h

end CasePAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring.CasePAux"

namespace FibreConstAux

theorem exists_point_factorsThrough_lift_residue
    {S : Type} [CommRing S] {A Kk : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (ι : Kk ⟶ A)
    [IsClosedImmersion ι] [IsFinite (ι ≫ f)] [Flat (ι ≫ f)]
    {L : Type} [Field L] [IsAlgClosed L] (O' : ValuationSubring L)
    (t : Spec (CommRingCat.of ↥O') ⟶ Spec (CommRingCat.of S))
    (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O')) ≫ t) f) (hQ : FactorsThrough ι Q) :
    ∃ P : {P : SchemeHomOver t f // FactorsThrough ι P},
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O')) ≫ P.1.1 = Q.1 := by
  classical
  obtain ⟨Q₀, hQ₀⟩ := hQ
  haveI : IsFinite (pullback.snd (ι ≫ f) t) := inferInstance
  haveI : Flat (pullback.snd (ι ≫ f) t) := inferInstance
  have wQ : Q₀ ≫ (ι ≫ f) = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O')) ≫ t := by
    rw [← Category.assoc, hQ₀, Q.2]
  obtain ⟨z, hz1, hz2⟩ :=
    AlgebraicGeometry.exists_section_comp_eq_of_finite_flat_valuationSubring O'
      (pullback.snd (ι ≫ f) t) (pullback.lift Q₀ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O'))) wQ)
      (pullback.lift_snd _ _ _)
  have hP : ((z ≫ pullback.fst (ι ≫ f) t) ≫ ι) ≫ f = t := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, hz1, Category.id_comp]
  refine ⟨⟨⟨(z ≫ pullback.fst (ι ≫ f) t) ≫ ι, hP⟩, ⟨z ≫ pullback.fst (ι ≫ f) t, rfl⟩⟩, ?_⟩
  show Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O')) ≫ ((z ≫ pullback.fst (ι ≫ f) t) ≫ ι) = Q.1
  rw [← Category.assoc, ← Category.assoc, hz2, pullback.lift_fst, hQ₀]

theorem caseP_red_surjective
    {S : Type} [CommRing S] {A Kk : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (ι : Kk ⟶ A)
    [IsClosedImmersion ι] [IsFinite (ι ≫ f)] [Flat (ι ≫ f)]
    {L : Type} [Field L] [IsAlgClosed L] (O' : ValuationSubring L)
    (t : Spec (CommRingCat.of ↥O') ⟶ Spec (CommRingCat.of S)) :
    Function.Surjective (CasePAux.compK (f := f) (t := t) ι
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O'))) rfl) := by
  intro Q
  obtain ⟨P, hP⟩ := exists_point_factorsThrough_lift_residue f ι O' t Q.1 Q.2
  exact ⟨P, Subtype.ext (Subtype.ext hP)⟩

end FibreConstAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring.CasePAux"

theorem caseP_red_bijective
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ)
    (𝒜 : FakeEllipticCurve Λ N ↥O)
    {Kk : Scheme.{0}} (ι : Kk ⟶ 𝒜.A) [IsClosedImmersion ι]
    [IsFinite (ι ≫ 𝒜.f)] [Flat (ι ≫ 𝒜.f)] [LocallyOfFinitePresentation (ι ≫ 𝒜.f)]
    (hsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → FactorsThrough ι Q →
        FactorsThrough ι (𝒜.L.mul t P Q) ∧ FactorsThrough ι (𝒜.L.inv t P))
    (hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)), FactorsThrough ι (𝒜.L.one t))
    (htors : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → nsmulPt 𝒜.L t ℓ P = 𝒜.L.one t)
    (O' : ValuationSubring (AlgebraicClosure ℚ)) (iO : ↥O →+* ↥O') (hiO : O'.subtype.comp iO = O.subtype)
    (hℓ : IsUnit ((ℓ : ℕ) : ↥O')) :
    Function.Bijective (CasePAux.compK (f := 𝒜.f) (t := Spec.map (CommRingCat.ofHom iO)) ι
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O'))) rfl) := by
  haveI : Smooth 𝒜.f := 𝒜.bundle.smooth
  constructor
  ·
    intro P₁ P₂ h
    have h' : GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O'))) rfl P₁.1 =
        GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O'))) rfl P₂.1 :=
      congrArg (fun P => (P.1 : SchemeHomOver _ 𝒜.f)) h
    letI G := 𝒜.L.pointGroup (Spec.map (CommRingCat.ofHom iO))
    letI G' := 𝒜.L.pointGroup (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O')) ≫ (Spec.map (CommRingCat.ofHom iO)))

    let red : SchemeHomOver (Spec.map (CommRingCat.ofHom iO)) 𝒜.f →* SchemeHomOver (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O')) ≫ (Spec.map (CommRingCat.ofHom iO))) 𝒜.f :=
      { toFun := GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O'))) rfl
        map_one' := 𝒜.L.one_natural (Spec.map (CommRingCat.ofHom iO)) _ _ rfl
        map_mul' := fun x y => 𝒜.L.mul_natural (Spec.map (CommRingCat.ofHom iO)) _ _ rfl x y }
    have hred_apply : ∀ x, red x = GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O'))) rfl x :=
      fun _ => rfl

    let D : SchemeHomOver (Spec.map (CommRingCat.ofHom iO)) 𝒜.f := P₁.1 * (P₂.1)⁻¹
    have hD_fac : FactorsThrough ι D := (hsub (Spec.map (CommRingCat.ofHom iO)) _ _ P₁.2 (hsub (Spec.map (CommRingCat.ofHom iO)) _ _ P₂.2 P₂.2).2).1
    have nsmul_eq : ∀ (n : ℕ) (P : SchemeHomOver (Spec.map (CommRingCat.ofHom iO)) 𝒜.f), nsmulPt 𝒜.L (Spec.map (CommRingCat.ofHom iO)) n P = 𝒜.L.nsmul (Spec.map (CommRingCat.ofHom iO)) n P := by
      intro n P; induction n with
      | zero => rfl
      | succ n ih => show 𝒜.L.mul (Spec.map (CommRingCat.ofHom iO)) (nsmulPt 𝒜.L (Spec.map (CommRingCat.ofHom iO)) n P) P = _; rw [ih]; rfl
    have hD_tors : 𝒜.L.IsTorsionPoint (Spec.map (CommRingCat.ofHom iO)) ℓ D := by
      rw [GoodReductionJacobian.RelativeGroupLaw.isTorsionPoint_def, ← nsmul_eq]; exact htors (Spec.map (CommRingCat.ofHom iO)) D hD_fac
    have hred : GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O'))) rfl D =
        GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O'))) rfl (𝒜.L.one (Spec.map (CommRingCat.ofHom iO))) := by
      rw [← hred_apply, ← hred_apply, show 𝒜.L.one (Spec.map (CommRingCat.ofHom iO)) = (1 : SchemeHomOver (Spec.map (CommRingCat.ofHom iO)) 𝒜.f) from rfl, map_one]
      show red (P₁.1 * (P₂.1)⁻¹) = 1
      rw [map_mul, map_inv, show red P₁.1 = red P₂.1 from h', mul_inv_cancel]
    have hD : D = 𝒜.L.one (Spec.map (CommRingCat.ofHom iO)) :=
      GoodReductionJacobian.RelativeGroupLaw.eq_one_of_isTorsionPoint_of_comp_residue_eq 𝒜.L 𝒜.comm (Spec.map (CommRingCat.ofHom iO)) ℓ hℓ D hD_tors hred
    apply Subtype.ext
    exact mul_inv_eq_one.mp hD
  ·
    exact FibreConstAux.caseP_red_surjective 𝒜.f ι O' (Spec.map (CommRingCat.ofHom iO))

namespace FibreConstAux

theorem existsUnique_point_factorsThrough_extend
    {S : Type} [CommRing S] {A Kk : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (ι : Kk ⟶ A)
    [IsClosedImmersion ι] [IsFinite (ι ≫ f)]
    {L : Type} [Field L] (O' : ValuationSubring L) (t : Spec (CommRingCat.of ↥O') ⟶ Spec (CommRingCat.of S))
    (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom O'.subtype) ≫ t) f) (hQ : FactorsThrough ι Q) :
    ∃! P : {P : SchemeHomOver t f // FactorsThrough ι P},
      Spec.map (CommRingCat.ofHom O'.subtype) ≫ P.1.1 = Q.1 := by
  classical
  obtain ⟨Q₀, hQ₀⟩ := hQ
  haveI : IsFinite (pullback.snd (ι ≫ f) t) := inferInstance
  have wQ : Q₀ ≫ (ι ≫ f) = Spec.map (CommRingCat.ofHom O'.subtype) ≫ t := by
    rw [← Category.assoc, hQ₀, Q.2]
  obtain ⟨z, ⟨hz1, hz2⟩, hzu⟩ :=
    AlgebraicGeometry.existsUnique_section_comp_eq_of_isFinite_valuationSubring O'
      (pullback.snd (ι ≫ f) t) (pullback.lift Q₀ (Spec.map (CommRingCat.ofHom O'.subtype)) wQ)
      (pullback.lift_snd _ _ _)
  have hP : ((z ≫ pullback.fst (ι ≫ f) t) ≫ ι) ≫ f = t := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, hz1, Category.id_comp]
  let P : {P : SchemeHomOver t f // FactorsThrough ι P} :=
    ⟨⟨(z ≫ pullback.fst (ι ≫ f) t) ≫ ι, hP⟩, ⟨z ≫ pullback.fst (ι ≫ f) t, rfl⟩⟩
  refine ⟨P, ?_, ?_⟩
  · show Spec.map (CommRingCat.ofHom O'.subtype) ≫ ((z ≫ pullback.fst (ι ≫ f) t) ≫ ι) = Q.1
    rw [← Category.assoc, ← Category.assoc, hz2, pullback.lift_fst, hQ₀]
  · rintro ⟨⟨P', hP'f⟩, ⟨P₀', hP₀'⟩⟩ hP'
    have wP' : P₀' ≫ (ι ≫ f) = 𝟙 _ ≫ t := by
      rw [← Category.assoc, hP₀', hP'f, Category.id_comp]
    have hQ₀' : Spec.map (CommRingCat.ofHom O'.subtype) ≫ P₀' = Q₀ := by
      rw [← cancel_mono ι, Category.assoc, hP₀', hQ₀]
      exact hP'
    have hz' : pullback.lift P₀' (𝟙 _) wP' = z := hzu _ ⟨pullback.lift_snd _ _ _, by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hQ₀']
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]⟩
    apply Subtype.ext; apply Subtype.ext
    show P' = (z ≫ pullback.fst (ι ≫ f) t) ≫ ι
    rw [← hz', pullback.lift_fst, hP₀']

end FibreConstAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring.CasePAux"

theorem caseP_gen_bijective
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ)
    (𝒜 : FakeEllipticCurve Λ N ↥O)
    {Kk : Scheme.{0}} (ι : Kk ⟶ 𝒜.A) [IsClosedImmersion ι]
    [IsFinite (ι ≫ 𝒜.f)] [Flat (ι ≫ 𝒜.f)] [LocallyOfFinitePresentation (ι ≫ 𝒜.f)]
    (hsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → FactorsThrough ι Q →
        FactorsThrough ι (𝒜.L.mul t P Q) ∧ FactorsThrough ι (𝒜.L.inv t P))
    (hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)), FactorsThrough ι (𝒜.L.one t))
    (htors : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → nsmulPt 𝒜.L t ℓ P = 𝒜.L.one t)
    (O' : ValuationSubring (AlgebraicClosure ℚ)) (iO : ↥O →+* ↥O') (hiO : O'.subtype.comp iO = O.subtype) :
    Function.Bijective (CasePAux.compK (f := 𝒜.f) (t := Spec.map (CommRingCat.ofHom iO)) ι
      (Spec.map (CommRingCat.ofHom O'.subtype)) rfl) := by

  constructor
  · intro P₁ P₂ h
    have h' : Spec.map (CommRingCat.ofHom O'.subtype) ≫ P₁.1.1 = Spec.map (CommRingCat.ofHom O'.subtype) ≫ P₂.1.1 :=
      congrArg (fun P => (P.1 : SchemeHomOver _ 𝒜.f).1) h
    obtain ⟨P, -, hu⟩ := FibreConstAux.existsUnique_point_factorsThrough_extend 𝒜.f ι O' (Spec.map (CommRingCat.ofHom iO))
      (CasePAux.compK (f := 𝒜.f) (t := Spec.map (CommRingCat.ofHom iO)) ι (Spec.map (CommRingCat.ofHom O'.subtype)) rfl P₂).1
      (CasePAux.compK (f := 𝒜.f) (t := Spec.map (CommRingCat.ofHom iO)) ι (Spec.map (CommRingCat.ofHom O'.subtype)) rfl P₂).2
    exact (hu P₁ h').trans (hu P₂ rfl).symm
  · intro Q
    obtain ⟨P, hP, -⟩ := FibreConstAux.existsUnique_point_factorsThrough_extend 𝒜.f ι O' (Spec.map (CommRingCat.ofHom iO)) Q.1 Q.2
    exact ⟨P, Subtype.ext (Subtype.ext hP)⟩

namespace FibreConstAux

theorem existsUnique_point_factorsThrough_descend'
    {S : Type} [CommRing S] {A Kk : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (ι : Kk ⟶ A)
    [IsClosedImmersion ι] [IsFinite (ι ≫ f)]
    {κ : Type} [Field κ] [IsAlgClosed κ] (sκ : S →+* κ) {k : Type} [Field k] (jκ : κ →+* k)
    (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom jκ) ≫ geomPoint κ sκ) f) (hQ : FactorsThrough ι Q) :
    ∃! P : {P : SchemeHomOver (geomPoint κ sκ) f // FactorsThrough ι P},
      Spec.map (CommRingCat.ofHom jκ) ≫ P.1.1 = Q.1 := by
  classical
  obtain ⟨Q₀, hQ₀⟩ := hQ
  haveI : IsFinite (pullback.snd (ι ≫ f) (geomPoint κ sκ)) := inferInstance
  have wQ : Q₀ ≫ (ι ≫ f) = Spec.map (CommRingCat.ofHom jκ) ≫ geomPoint κ sκ := by
    rw [← Category.assoc, hQ₀, Q.2]
  obtain ⟨z, ⟨hz1, hz2⟩, hzu⟩ :=
    AlgebraicGeometry.existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed jκ
      (pullback.snd (ι ≫ f) (geomPoint κ sκ)) (pullback.lift Q₀ (Spec.map (CommRingCat.ofHom jκ)) wQ)
      (pullback.lift_snd _ _ _)
  have hP : ((z ≫ pullback.fst (ι ≫ f) (geomPoint κ sκ)) ≫ ι) ≫ f = geomPoint κ sκ := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, hz1, Category.id_comp]
  let P : {P : SchemeHomOver (geomPoint κ sκ) f // FactorsThrough ι P} :=
    ⟨⟨(z ≫ pullback.fst (ι ≫ f) (geomPoint κ sκ)) ≫ ι, hP⟩, ⟨z ≫ pullback.fst (ι ≫ f) (geomPoint κ sκ), rfl⟩⟩
  refine ⟨P, ?_, ?_⟩
  · show Spec.map (CommRingCat.ofHom jκ) ≫ ((z ≫ pullback.fst (ι ≫ f) (geomPoint κ sκ)) ≫ ι) = Q.1
    rw [← Category.assoc, ← Category.assoc, hz2, pullback.lift_fst, hQ₀]
  · rintro ⟨⟨P', hP'f⟩, ⟨P₀', hP₀'⟩⟩ hP'
    have wP' : P₀' ≫ (ι ≫ f) = 𝟙 _ ≫ geomPoint κ sκ := by
      rw [← Category.assoc, hP₀', hP'f, Category.id_comp]
    have hQ₀' : Spec.map (CommRingCat.ofHom jκ) ≫ P₀' = Q₀ := by
      rw [← cancel_mono ι, Category.assoc, hP₀', hQ₀]
      exact hP'
    have hz' : pullback.lift P₀' (𝟙 _) wP' = z := hzu _ ⟨pullback.lift_snd _ _ _, by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hQ₀']
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]⟩
    apply Subtype.ext; apply Subtype.ext
    show P' = (z ≫ pullback.fst (ι ≫ f) (geomPoint κ sκ)) ≫ ι
    rw [← hz', pullback.lift_fst, hP₀']

end FibreConstAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring.CasePAux"

theorem caseP_field_bijective
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ)
    (𝒜 : FakeEllipticCurve Λ N ↥O)
    {Kk : Scheme.{0}} (ι : Kk ⟶ 𝒜.A) [IsClosedImmersion ι]
    [IsFinite (ι ≫ 𝒜.f)] [Flat (ι ≫ 𝒜.f)] [LocallyOfFinitePresentation (ι ≫ 𝒜.f)]
    (hsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → FactorsThrough ι Q →
        FactorsThrough ι (𝒜.L.mul t P Q) ∧ FactorsThrough ι (𝒜.L.inv t P))
    (hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)), FactorsThrough ι (𝒜.L.one t))
    (htors : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → nsmulPt 𝒜.L t ℓ P = 𝒜.L.one t)
    (κ : Type) [Field κ] [IsAlgClosed κ] (sκ : ↥O →+* κ)
    (k' : Type) [Field k'] (jk : κ →+* k') :
    Function.Bijective (CasePAux.compK (f := 𝒜.f) (t := geomPoint κ sκ) ι (Spec.map (CommRingCat.ofHom jk)) rfl) := by

  constructor
  · intro P₁ P₂ h
    have h' : Spec.map (CommRingCat.ofHom jk) ≫ P₁.1.1 = Spec.map (CommRingCat.ofHom jk) ≫ P₂.1.1 :=
      congrArg (fun P => (P.1 : SchemeHomOver _ 𝒜.f).1) h
    obtain ⟨P, -, hu⟩ := FibreConstAux.existsUnique_point_factorsThrough_descend' 𝒜.f ι sκ jk
      (CasePAux.compK (f := 𝒜.f) (t := geomPoint κ sκ) ι (Spec.map (CommRingCat.ofHom jk)) rfl P₂).1
      (CasePAux.compK (f := 𝒜.f) (t := geomPoint κ sκ) ι (Spec.map (CommRingCat.ofHom jk)) rfl P₂).2
    exact (hu P₁ h').trans (hu P₂ rfl).symm
  · intro Q
    obtain ⟨P, hP, -⟩ := FibreConstAux.existsUnique_point_factorsThrough_descend' 𝒜.f ι sκ jk Q.1 Q.2
    exact ⟨P, Subtype.ext (Subtype.ext hP)⟩

theorem caseP
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ)
    (𝒜 : FakeEllipticCurve Λ N ↥O) (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (K : E.ExtraLevel ℓ)
    {Kk : Scheme.{0}} (ι : Kk ⟶ 𝒜.A) [IsClosedImmersion ι]
    [IsFinite (ι ≫ 𝒜.f)] [Flat (ι ≫ 𝒜.f)] [LocallyOfFinitePresentation (ι ≫ 𝒜.f)]
    (hrank : ∀ s : ↥(Spec (CommRingCat.of ↥O)), (ι ≫ 𝒜.f).finrank s = ℓ ^ 2)
    (hsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → FactorsThrough ι Q →
        FactorsThrough ι (𝒜.L.mul t P Q) ∧ FactorsThrough ι (𝒜.L.inv t P))
    (hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)), FactorsThrough ι (𝒜.L.one t))
    (htors : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → nsmulPt 𝒜.L t ℓ P = 𝒜.L.one t)
    (hgen : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t' E.f),
      FactorsThrough K.levK P ↔ ∃ P₀ : T ⟶ Kk, P₀ ≫ ι = P.1 ≫ gE)
    (k : Type) [Field k] [IsAlgClosed k] (sk : ↥O →+* k) (hℓ : (ℓ : k) ≠ 0)
    (hker : RingHom.ker sk ≠ ⊥) :
      ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (geomPoint k sk) 𝒜.f // FactorsThrough ι P},
        ∀ x y : ZMod ℓ × ZMod ℓ, (e (x + y) : SchemeHomOver (geomPoint k sk) 𝒜.f) =
          𝒜.L.mul (geomPoint k sk) (e x) (e y) := by
  classical

  haveI h𝔭 : (RingHom.ker sk).IsPrime := RingHom.ker_isPrime sk
  let O' : ValuationSubring (AlgebraicClosure ℚ) := O.ofPrime (RingHom.ker sk)
  let iO : ↥O →+* ↥O' := algebraMap ↥O ↥O'
  have hiO : O'.subtype.comp iO = O.subtype := by ext x; rfl
  have hunits : ∀ y : (RingHom.ker sk).primeCompl, IsUnit (sk (y : ↥O)) := fun y =>
    isUnit_iff_ne_zero.mpr (fun h0 => y.2 h0)
  let τ : ↥O' →+* k := IsLocalization.lift (M := (RingHom.ker sk).primeCompl) (S := ↥O') hunits
  have hτ : τ.comp iO = sk := IsLocalization.lift_comp (M := (RingHom.ker sk).primeCompl) hunits
  have hτmax : ∀ x ∈ IsLocalRing.maximalIdeal ↥O', τ x = 0 := by
    intro x hx
    have hmax : IsLocalRing.maximalIdeal ↥O' = Ideal.map iO (RingHom.ker sk) :=
      (IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker sk) ↥O').symm
    rw [hmax] at hx
    have h1 : τ x ∈ Ideal.map τ (Ideal.map iO (RingHom.ker sk)) := Ideal.mem_map_of_mem τ hx
    rw [Ideal.map_map, hτ] at h1
    have h2 : Ideal.map sk (RingHom.ker sk) ≤ ⊥ := by
      rw [Ideal.map_le_iff_le_comap]; exact fun y hy => hy
    exact h2 h1
  let τbar : IsLocalRing.ResidueField ↥O' →+* k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥O') τ hτmax
  have hτbar : τbar.comp (IsLocalRing.residue ↥O') = τ := RingHom.ext fun _ => rfl
  have hsk : (τbar.comp (IsLocalRing.residue ↥O')).comp iO = sk := by rw [hτbar, hτ]
  have hℓO : ((ℓ : ℕ) : ↥O) ∈ (RingHom.ker sk).primeCompl := by
    show ((ℓ : ℕ) : ↥O) ∉ RingHom.ker sk
    rw [RingHom.mem_ker, map_natCast]; exact hℓ
  have hℓ' : IsUnit ((ℓ : ℕ) : ↥O') := by
    have := IsLocalization.map_units (M := (RingHom.ker sk).primeCompl) ↥O' ⟨_, hℓO⟩
    rwa [show algebraMap ↥O ↥O' ((ℓ : ℕ) : ↥O) = ((ℓ : ℕ) : ↥O') from map_natCast _ ℓ] at this
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥O') := ValuationSubring.isAlgClosed_residueField O'

  obtain ⟨e2, he2⟩ := CasePAux.isMul_of_bijective 𝒜.L ι hsub _ _ _ rfl
    (caseP_red_bijective O ℓ 𝒜 ι hsub hone htors O' iO hiO hℓ')
  obtain ⟨e3, he3⟩ := CasePAux.isMul_of_bijective 𝒜.L ι hsub _ _ _ rfl
    (caseP_gen_bijective O ℓ 𝒜 ι hsub hone htors O' iO hiO)
  obtain ⟨e4, he4⟩ := CasePAux.isMul_of_bijective 𝒜.L ι hsub _ _ _ rfl
    (caseP_field_bijective O ℓ 𝒜 ι hsub hone htors (IsLocalRing.ResidueField ↥O') ((IsLocalRing.residue ↥O').comp iO) k τbar)

  have hL : geomPoint (AlgebraicClosure ℚ) O.subtype = Spec.map (CommRingCat.ofHom O'.subtype) ≫ Spec.map (CommRingCat.ofHom iO) := by
    show Spec.map _ = _; rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hiO]
  have hκ : Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O')) ≫ Spec.map (CommRingCat.ofHom iO) =
      geomPoint (IsLocalRing.ResidueField ↥O') ((IsLocalRing.residue ↥O').comp iO) := by
    show _ = Spec.map _; rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hk : Spec.map (CommRingCat.ofHom τbar) ≫ geomPoint (IsLocalRing.ResidueField ↥O') ((IsLocalRing.residue ↥O').comp iO) =
      geomPoint k sk := by
    show _ ≫ Spec.map _ = Spec.map _; rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hsk]
  obtain ⟨eL, heL⟩ := CasePAux.isMul_of_eq 𝒜.L ι hsub _ _ hL
  obtain ⟨eκ, heκ⟩ := CasePAux.isMul_of_eq 𝒜.L ι hsub _ _ hκ
  obtain ⟨ek, hek⟩ := CasePAux.isMul_of_eq 𝒜.L ι hsub _ _ hk

  have hℓQ : ((ℓ : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by
    have : (ℓ : ℕ) ≠ 0 := by rintro rfl; exact hℓ (by simp)
    exact_mod_cast this
  obtain ⟨e0, he0⟩ := caseZero O ℓ 𝒜 E gE hgE hgE_mul K ι hrank hsub hone htors hgen (AlgebraicClosure ℚ) O.subtype hℓQ
    Subtype.val_injective

  refine ⟨e0.trans (eL.trans (e3.symm.trans (e2.trans (eκ.trans (e4.trans ek))))), ?_⟩
  exact CasePAux.param_trans 𝒜.L ι hsub e0 he0
    (heL.trans 𝒜.L ι hsub ((he3.symm 𝒜.L ι hsub).trans 𝒜.L ι hsub (he2.trans 𝒜.L ι hsub (heκ.trans 𝒜.L ι hsub (he4.trans 𝒜.L ι hsub hek)))))

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ)
    (𝒜 : FakeEllipticCurve Λ N ↥O) (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (K : E.ExtraLevel ℓ)
    {Kk : Scheme.{0}} (ι : Kk ⟶ 𝒜.A) [IsClosedImmersion ι]
    [IsFinite (ι ≫ 𝒜.f)] [Flat (ι ≫ 𝒜.f)] [LocallyOfFinitePresentation (ι ≫ 𝒜.f)]
    (hrank : ∀ s : ↥(Spec (CommRingCat.of ↥O)), (ι ≫ 𝒜.f).finrank s = ℓ ^ 2)
    (hsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → FactorsThrough ι Q →
        FactorsThrough ι (𝒜.L.mul t P Q) ∧ FactorsThrough ι (𝒜.L.inv t P))
    (hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)), FactorsThrough ι (𝒜.L.one t))
    (htors : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → nsmulPt 𝒜.L t ℓ P = 𝒜.L.one t)
    (hgen : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t' E.f),
      FactorsThrough K.levK P ↔ ∃ P₀ : T ⟶ Kk, P₀ ≫ ι = P.1 ≫ gE) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : ↥O →+* k), (ℓ : k) ≠ 0 →
      ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (geomPoint k sk) 𝒜.f // FactorsThrough ι P},
        ∀ x y : ZMod ℓ × ZMod ℓ, (e (x + y) : SchemeHomOver (geomPoint k sk) 𝒜.f) =
          𝒜.L.mul (geomPoint k sk) (e x) (e y) := by
  intro k _ _ sk hℓ
  by_cases hinj : Function.Injective sk
  · exact caseZero O ℓ 𝒜 E gE hgE hgE_mul K ι hrank hsub hone htors hgen k sk hℓ hinj
  · exact caseP O ℓ 𝒜 E gE hgE hgE_mul K ι hrank hsub hone htors hgen k sk hℓ (fun h => hinj ((RingHom.injective_iff_ker_eq_bot sk).mpr h))

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring (solution)
