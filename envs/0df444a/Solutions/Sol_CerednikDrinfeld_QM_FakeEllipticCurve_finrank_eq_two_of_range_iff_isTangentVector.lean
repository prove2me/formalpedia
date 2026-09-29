-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.finrank_eq_two_of_range_iff_isTangentVector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c0abb0bb-fe79-57be-81b5-d17360d4562a

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_finrank_cotangentSpace_eq
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_tangentPoints_equiv_linearMap_cotangentSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_finrank_eq_two_of_range_iff_isTangentVector
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian CerednikDrinfeld.QM"
open scoped Quaternion

universe u

namespace D2aTandim

section GroupLaw

variable {K : Type u} [Field K] {X : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of K)}
variable (L : RelativeGroupLaw K x)
variable {V : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
variable {W : Type u} [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
variable {W' : Type u} [AddCommGroup W'] [Module K W'] [Module Kᵐᵒᵖ W'] [IsCentralScalar K W']

abbrev unitPt : Spec (CommRingCat.of K) ⟶ X := (L.one (𝟙 _)).1

theorem unitPt_over : unitPt L ≫ x = 𝟙 _ := (L.one (𝟙 _)).2

theorem one_toBase_coe : (L.one (SquareZero.toBase K V)).1 = SquareZero.toBase K V ≫ unitPt L := by
  have h := L.one_natural (𝟙 _) (SquareZero.toBase K V) (SquareZero.toBase K V) (Category.comp_id _)
  exact (congrArg Subtype.val h).symm

def toPt (v : TangentPoints x (unitPt L) V) : SchemeHomOver (SquareZero.toBase K V) x := ⟨v.1, v.2.1⟩

@[scoped simp] theorem toPt_coe (v : TangentPoints x (unitPt L) V) : (toPt L v).1 = v.1 := rfl

theorem toPt_injective : Function.Injective (toPt L (V := V)) := by
  intro v w h
  have h' : (toPt L v).1 = (toPt L w).1 := congrArg Subtype.val h
  exact TangentPoints.ext h'

theorem comp_basePoint_toPt (v : TangentPoints x (unitPt L) V) :
    schemeHomOverComp (SquareZero.basePoint K V) (SquareZero.basePoint_toBase K V) (toPt L v) = L.one (𝟙 _) :=
  Subtype.ext v.2.2

def mulT (v w : TangentPoints x (unitPt L) V) : TangentPoints x (unitPt L) V :=
  ⟨(L.mul (SquareZero.toBase K V) (toPt L v) (toPt L w)).1, (L.mul _ _ _).2, by
    have h := L.mul_natural (SquareZero.toBase K V) (𝟙 _) (SquareZero.basePoint K V)
      (SquareZero.basePoint_toBase K V) (toPt L v) (toPt L w)
    rw [comp_basePoint_toPt, comp_basePoint_toPt, L.mul_one] at h
    exact congrArg Subtype.val h⟩

@[scoped simp] theorem mulT_coe (v w : TangentPoints x (unitPt L) V) :
    (mulT L v w).1 = (L.mul (SquareZero.toBase K V) (toPt L v) (toPt L w)).1 := rfl

theorem toPt_mulT (v w : TangentPoints x (unitPt L) V) :
    toPt L (mulT L v w) = L.mul (SquareZero.toBase K V) (toPt L v) (toPt L w) := rfl

private theorem _root_.D2aTandim.map_comp (v : TangentPoints x (unitPt L) V) (φ : V →ₗ[K] W) (ψ : W →ₗ[K] W') :
    (v.map φ).map ψ = v.map (ψ ∘ₗ φ) := by
  apply TangentPoints.ext
  simp only [TangentPoints.map_coe, SquareZero.specMap_comp, Category.assoc]

p2m_export "D2aTandim" "map_comp"
theorem map_id' (v : TangentPoints x (unitPt L) V) : v.map (LinearMap.id : V →ₗ[K] V) = v := by
  apply TangentPoints.ext
  simp only [TangentPoints.map_coe, SquareZero.specMap_id, Category.id_comp]

theorem specMap_zero : SquareZero.specMap K (0 : V →ₗ[K] W) = SquareZero.toBase K W ≫ SquareZero.basePoint K V := by
  rw [SquareZero.specMap, SquareZero.toBase, SquareZero.basePoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  change TrivSqZeroExt.map (0 : V →ₗ[K] W) a = algebraMap K (TrivSqZeroExt K W) (TrivSqZeroExt.fstHom K K V a)
  rw [TrivSqZeroExt.algebraMap_eq_inl]
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [TrivSqZeroExt.fstHom]
  · simp [TrivSqZeroExt.fstHom]

theorem toPt_map_zero (v : TangentPoints x (unitPt L) V) :
    toPt L (v.map (0 : V →ₗ[K] W)) = L.one (SquareZero.toBase K W) := by
  apply Subtype.ext
  rw [toPt_coe, TangentPoints.map_coe, specMap_zero, Category.assoc, v.2.2, one_toBase_coe]

theorem mulT_map (v w : TangentPoints x (unitPt L) V) (φ : V →ₗ[K] W) :
    (mulT L v w).map φ = mulT L (v.map φ) (w.map φ) := by
  apply TangentPoints.ext
  have h := L.mul_natural (SquareZero.toBase K V) (SquareZero.toBase K W) (SquareZero.specMap K φ)
    (SquareZero.specMap_toBase K φ) (toPt L v) (toPt L w)
  have h' := congrArg Subtype.val h
  exact h'

theorem mulT_of_right_eq_one (v w : TangentPoints x (unitPt L) V) (hw : toPt L w = L.one _) : mulT L v w = v := by
  apply toPt_injective L
  rw [toPt_mulT, hw, L.mul_one]

theorem mulT_of_left_eq_one (v w : TangentPoints x (unitPt L) V) (hv : toPt L v = L.one _) : mulT L v w = w := by
  apply toPt_injective L
  rw [toPt_mulT, hv, L.one_mul]

theorem gamma_mulT {C : Type u} [AddCommGroup C] [Module K C]
    (γ : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V],
      TangentPoints x (unitPt L) V ≃ (C →ₗ[K] V))
    (hγ : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
      (W : Type u) [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
      (φ : V →ₗ[K] W) (v : TangentPoints x (unitPt L) V), γ W (v.map φ) = φ ∘ₗ γ V v)
    (t₁ t₂ : TangentPoints x (unitPt L) K) :
    γ K (mulT L t₁ t₂) = γ K t₁ + γ K t₂ := by
  set u : TangentPoints x (unitPt L) (K × K) :=
    mulT L (t₁.map (LinearMap.inl K K K)) (t₂.map (LinearMap.inr K K K)) with hu
  have h1 : u.map (LinearMap.fst K K K) = t₁ := by
    rw [hu, mulT_map, map_comp, map_comp, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, map_id']
    exact mulT_of_right_eq_one L _ _ (toPt_map_zero L t₂)
  have h2 : u.map (LinearMap.snd K K K) = t₂ := by
    rw [hu, mulT_map, map_comp, map_comp, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, map_id']
    exact mulT_of_left_eq_one L _ _ (toPt_map_zero L t₁)
  have h3 : u.map (LinearMap.fst K K K + LinearMap.snd K K K) = mulT L t₁ t₂ := by
    rw [hu, mulT_map, map_comp, map_comp, LinearMap.add_comp, LinearMap.add_comp, LinearMap.fst_comp_inl,
      LinearMap.snd_comp_inl, LinearMap.fst_comp_inr, LinearMap.snd_comp_inr, add_zero, zero_add, map_id', map_id']
  calc γ K (mulT L t₁ t₂) = γ K (u.map (LinearMap.fst K K K + LinearMap.snd K K K)) := by rw [h3]
    _ = (LinearMap.fst K K K + LinearMap.snd K K K) ∘ₗ γ (K × K) u := hγ _ _ _ _
    _ = LinearMap.fst K K K ∘ₗ γ (K × K) u + LinearMap.snd K K K ∘ₗ γ (K × K) u := LinearMap.add_comp _ _ _
    _ = γ K (u.map (LinearMap.fst K K K)) + γ K (u.map (LinearMap.snd K K K)) := by rw [hγ, hγ]
    _ = γ K t₁ + γ K t₂ := by rw [h1, h2]

theorem gamma_map_smul {C : Type u} [AddCommGroup C] [Module K C]
    (γ : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V],
      TangentPoints x (unitPt L) V ≃ (C →ₗ[K] V))
    (hγ : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
      (W : Type u) [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
      (φ : V →ₗ[K] W) (v : TangentPoints x (unitPt L) V), γ W (v.map φ) = φ ∘ₗ γ V v)
    (c : K) (t : TangentPoints x (unitPt L) K) :
    γ K (t.map (c • (LinearMap.id : K →ₗ[K] K))) = c • γ K t := by
  rw [hγ, LinearMap.smul_comp, LinearMap.id_comp]

end GroupLaw

section BaseChange

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
variable {B : Type} [CommRing B] (E : FakeEllipticCurve Λ N B) {k : Type} [Field k] (sk : B →+* k)
variable (E' : FakeEllipticCurve Λ N k) (g : E'.A ⟶ E.A)
variable (hg : IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom sk)))

theorem tangentBase_eq : tangentBase k sk = SquareZero.toBase k k ≫ Spec.map (CommRingCat.ofHom sk) := by
  rw [tangentBase, SquareZero.toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

def pushG {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t' E'.f) :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom sk)) E.f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem pushG_coe {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t' E'.f) :
    (pushG E sk E' g hg P).1 = P.1 ≫ g := rfl

variable (hgmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t' E'.f),
  (E'.L.mul t' P Q).1 ≫ g =
    (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom sk))
      ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)

include hgmul

theorem pushG_mul {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t' E'.f) :
    pushG E sk E' g hg (E'.L.mul t' P Q) = E.L.mul _ (pushG E sk E' g hg P) (pushG E sk E' g hg Q) :=
  Subtype.ext (hgmul t' P Q)

theorem pushG_one {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of k)) :
    pushG E sk E' g hg (E'.L.one t') = E.L.one _ := by
  set t := t' ≫ Spec.map (CommRingCat.ofHom sk)
  set o := pushG E sk E' g hg (E'.L.one t') with ho
  have h : E.L.mul t o o = o := by
    rw [ho, ← pushG_mul E sk E' g hg hgmul, E'.L.one_mul]
  calc o = E.L.mul t (E.L.one t) o := (E.L.one_mul t _).symm
    _ = E.L.mul t (E.L.mul t (E.L.inv t o) o) o := by rw [E.L.inv_mul_cancel]
    _ = E.L.mul t (E.L.inv t o) (E.L.mul t o o) := by rw [E.L.mul_assoc]
    _ = E.L.mul t (E.L.inv t o) o := by rw [h]
    _ = E.L.one t := E.L.inv_mul_cancel t _

theorem unitPt_comp_g : unitPt E'.L ≫ g = (E.L.one (geomPoint k sk)).1 := by
  have h := congrArg Subtype.val (pushG_one E sk E' g hg hgmul (𝟙 _))
  rw [pushG_coe] at h
  rw [h]
  have e : (𝟙 _ ≫ Spec.map (CommRingCat.ofHom sk)) = geomPoint k sk := Category.id_comp _
  exact congrArg (fun t => (E.L.one t).1) e

omit hgmul in

theorem mul_coe_congr {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of B)} (h : t = t')
    (P Q : SchemeHomOver t E.f) (P' Q' : SchemeHomOver t' E.f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (E.L.mul t P Q).1 = (E.L.mul t' P' Q').1 := by
  subst h
  cases Subtype.ext hP
  cases Subtype.ext hQ
  rfl

omit hgmul in

noncomputable def liftT (P : SchemeHomOver (tangentBase k sk) E.f) (hP : IsTangentVector E.L k sk P)
    (hunit : unitPt E'.L ≫ g = (E.L.one (geomPoint k sk)).1) :
    TangentPoints E'.f (unitPt E'.L) k :=
  ⟨hg.lift P.1 (SquareZero.toBase k k) (by rw [P.2, tangentBase_eq]),
    ⟨hg.lift_snd _ _ _, by
      apply hg.hom_ext
      · rw [Category.assoc, hg.lift_fst, hunit]
        exact hP
      · rw [Category.assoc, hg.lift_snd, SquareZero.basePoint_toBase, unitPt_over]⟩⟩

omit hgmul in
@[scoped simp] theorem liftT_coe_comp_g (P : SchemeHomOver (tangentBase k sk) E.f) (hP : IsTangentVector E.L k sk P)
    (hunit : unitPt E'.L ≫ g = (E.L.one (geomPoint k sk)).1) :
    (liftT E sk E' g hg P hP hunit).1 ≫ g = P.1 :=
  hg.lift_fst _ _ _

omit hgmul in

def descT (w : TangentPoints E'.f (unitPt E'.L) k) : SchemeHomOver (tangentBase k sk) E.f :=
  ⟨w.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, w.2.1, tangentBase_eq]⟩

omit hgmul in
@[scoped simp] theorem descT_coe (w : TangentPoints E'.f (unitPt E'.L) k) : (descT E sk E' g hg w).1 = w.1 ≫ g := rfl

theorem isTangentVector_descT (w : TangentPoints E'.f (unitPt E'.L) k) :
    IsTangentVector E.L k sk (descT E sk E' g hg w) := by
  change SquareZero.basePoint k k ≫ w.1 ≫ g = _
  rw [← Category.assoc, w.2.2, unitPt_comp_g E sk E' g hg hgmul]

omit hgmul in
theorem descT_liftT (P : SchemeHomOver (tangentBase k sk) E.f) (hP : IsTangentVector E.L k sk P)
    (hunit : unitPt E'.L ≫ g = (E.L.one (geomPoint k sk)).1) :
    descT E sk E' g hg (liftT E sk E' g hg P hP hunit) = P :=
  Subtype.ext (hg.lift_fst _ _ _)

omit hgmul in
theorem liftT_descT (w : TangentPoints E'.f (unitPt E'.L) k)
    (hP : IsTangentVector E.L k sk (descT E sk E' g hg w))
    (hunit : unitPt E'.L ≫ g = (E.L.one (geomPoint k sk)).1) :
    liftT E sk E' g hg (descT E sk E' g hg w) hP hunit = w := by
  apply TangentPoints.ext
  apply hg.hom_ext
  · rw [liftT_coe_comp_g, descT_coe]
  · change hg.lift _ _ _ ≫ E'.f = w.1 ≫ E'.f
    rw [hg.lift_snd, w.2.1]

omit hgmul in
theorem descT_injective : Function.Injective (descT E sk E' g hg) := by
  intro w w' h
  apply TangentPoints.ext
  apply hg.hom_ext
  · exact congrArg Subtype.val h
  · rw [w.2.1, w'.2.1]

theorem descT_mulT (w₁ w₂ : TangentPoints E'.f (unitPt E'.L) k) :
    descT E sk E' g hg (mulT E'.L w₁ w₂) =
      E.L.mul (tangentBase k sk) (descT E sk E' g hg w₁) (descT E sk E' g hg w₂) := by
  apply Subtype.ext
  rw [descT_coe, mulT_coe, hgmul]
  exact mul_coe_congr E (tangentBase_eq sk).symm _ _ _ _ rfl rfl

omit hgmul in
theorem descT_map_smul (c : k) (w : TangentPoints E'.f (unitPt E'.L) k) :
    (descT E sk E' g hg (w.map (c • (LinearMap.id : k →ₗ[k] k)))).1 = tangentScale k c ≫ (descT E sk E' g hg w).1 := by
  rw [descT_coe, descT_coe, TangentPoints.map_coe, Category.assoc]
  rfl

end BaseChange

section Rational

variable {K : Type u} [Field K]

theorem surjective_residueFieldMap_of_section {X Y : Scheme.{u}} (f : X ⟶ Y) (z : Y ⟶ X)
    (hz : z ≫ f = 𝟙 Y) (y : Y) :
    Function.Surjective (f.residueFieldMap (z.base y)) := by
  have h1 : (z ≫ f).residueFieldMap y = f.residueFieldMap (z.base y) ≫ z.residueFieldMap y :=
    Scheme.residueFieldMap_comp z f y
  have hy : (z ≫ f).base y = (𝟙 Y : Y ⟶ Y).base y := by rw [hz]
  set ε := Y.residueFieldCongr hy with hε
  have h2 : (z ≫ f).residueFieldMap y = ε.hom ≫ (𝟙 Y : Y ⟶ Y).residueFieldMap y :=
    Scheme.Hom.residueFieldMap_congr hz y
  have key : f.residueFieldMap (z.base y) ≫ z.residueFieldMap y = ε.hom ≫ (𝟙 Y : Y ⟶ Y).residueFieldMap y :=
    h1.symm.trans h2
  rw [Scheme.residueFieldMap_id] at key
  intro c
  refine ⟨ε.inv (z.residueFieldMap y c), ?_⟩
  apply (z.residueFieldMap y).hom.injective
  have h3 := congrArg (fun φ => φ.hom (ε.inv (z.residueFieldMap y c))) key
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h3
  rw [h3]
  change (ε.inv ≫ ε.hom ≫ 𝟙 _).hom (z.residueFieldMap y c) = _
  rw [Iso.inv_hom_id_assoc]
  rfl

theorem surjective_evaluation_top_Spec_field (K : Type u) [Field K] (y : Spec (CommRingCat.of K)) :
    Function.Surjective ((Spec (CommRingCat.of K)).evaluation ⊤ y trivial) := by
  have hy : y.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  haveI : y.asIdeal.IsMaximal := by rw [hy]; exact Ideal.bot_isMaximal
  have hs : Function.Surjective (algebraMap K y.asIdeal.ResidueField) :=
    Ideal.algebraMap_residueField_surjective _
  have key := Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of K) y
  have h1 : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec (CommRingCat.of K)).presheaf.germ ⊤ y trivial ≫ (Spec (CommRingCat.of K)).residue y) := by
    rw [← key]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (Scheme.Spec.residueFieldIso (CommRingCat.of K) y).symm.commRingCatIsoToRingEquiv.surjective.comp hs
  intro c
  obtain ⟨a, ha⟩ := h1 c
  exact ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).inv a, ha⟩

theorem bijective_algebraMap_residueField {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (pt : Spec (CommRingCat.of K) ⟶ X) (hpt : pt ≫ x = 𝟙 _) :
    letI : Algebra K (X.presheaf.stalk (pt.base (IsLocalRing.closedPoint K))) :=
      ((X.presheaf.germ ⊤ (pt.base (IsLocalRing.closedPoint K)) trivial).hom.comp
        (x.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
    Function.Bijective (algebraMap K
      (IsLocalRing.ResidueField (X.presheaf.stalk (pt.base (IsLocalRing.closedPoint K))))) := by
  set p := pt.base (IsLocalRing.closedPoint K)
  letI : Algebra K (X.presheaf.stalk p) :=
    ((X.presheaf.germ ⊤ p trivial).hom.comp (x.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
  have hcomp : algebraMap K (IsLocalRing.ResidueField (X.presheaf.stalk p)) =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Spec (CommRingCat.of K)).evaluation ⊤ (x.base p) trivial ≫
        x.residueFieldMap p).hom := by
    rw [IsScalarTower.algebraMap_eq K (X.presheaf.stalk p) (IsLocalRing.ResidueField _),
      IsLocalRing.ResidueField.algebraMap_eq, Scheme.evaluation_naturality x p (V := ⊤) trivial]
    rfl
  constructor
  · exact RingHom.injective _
  · rw [hcomp]
    simp only [CommRingCat.hom_comp]
    exact ((surjective_residueFieldMap_of_section x pt hpt _).comp
      (surjective_evaluation_top_Spec_field K (x.base p))).comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective

theorem finrank_cotangentSpace_residueField_eq {S : Type u} [CommRing S] [IsLocalRing S] [Algebra K S]
    (hK : Function.Bijective (algebraMap K (IsLocalRing.ResidueField S))) :
    Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.CotangentSpace S) =
      Module.finrank K (IsLocalRing.CotangentSpace S) := by
  symm
  unfold Module.finrank
  congr 1
  refine rank_eq_of_equiv_equiv (algebraMap K (IsLocalRing.ResidueField S)) (AddEquiv.refl _) hK ?_
  intro r m
  change r • m = (algebraMap K (IsLocalRing.ResidueField S) r) • m
  rw [IsScalarTower.algebraMap_apply K S (IsLocalRing.ResidueField S) r, IsScalarTower.algebraMap_smul,
    IsScalarTower.algebraMap_smul]

end Rational

end D2aTandim
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_finrank_eq_two_of_range_iff_isTangentVector.D2aTandim"

open D2aTandim in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B : Type) [CommRing B] (E : FakeEllipticCurve Λ N B) (k : Type) [Field k] (sk : B →+* k)
    (V : Type) [AddCommGroup V] [Module k V] (τ : V → SchemeHomOver (tangentBase k sk) E.f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P, P ∈ Set.range τ ↔ IsTangentVector E.L k sk P)
    (hadd : ∀ v w, τ (v + w) = E.L.mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) :
    Module.finrank k V = 2 := by
  classical

  obtain ⟨E', g, hg, hgmul, -, -, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff sk E
  have hunit : unitPt E'.L ≫ g = (E.L.one (geomPoint k sk)).1 :=
    unitPt_comp_g E sk E' g hg (fun t' P Q => hgmul t' P Q)

  set z : Spec (CommRingCat.of k) ⟶ E'.A := unitPt E'.L with hzdef
  have hz : z ≫ E'.f = 𝟙 _ := unitPt_over E'.L
  set p := z.base (IsLocalRing.closedPoint k) with hpdef
  letI : Algebra k (E'.A.presheaf.stalk p) :=
    ((E'.A.presheaf.germ ⊤ p trivial).hom.comp
      (E'.f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra

  haveI hsm : Smooth E'.f := E'.bundle.smooth
  haveI hsm2 : SmoothOfRelativeDimension 2 E'.f :=
    CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two k E'
  haveI hint : IsIntegral E'.A := GoodReductionJacobian.AbelianSchemePropertyBundle.isIntegral_of_field E'.bundle

  set n := Module.finrank (IsLocalRing.ResidueField (E'.A.presheaf.stalk p))
    (IsLocalRing.CotangentSpace (E'.A.presheaf.stalk p)) with hndef
  haveI hsmn : SmoothOfRelativeDimension n E'.f :=
    AlgebraicGeometry.smoothOfRelativeDimension_of_finrank_cotangentSpace_eq E'.f z hz n rfl
  have hn2 : n = 2 := by
    have h1 : (n : WithBot ℕ∞) ≤ topologicalKrullDim E'.A :=
      AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim E'.f n
    have h2 : topologicalKrullDim E'.A ≤ (2 : ℕ) :=
      AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le E'.f 2
    have h3 : ((2 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim E'.A :=
      AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim E'.f 2
    have h4 : topologicalKrullDim E'.A ≤ (n : ℕ) :=
      AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le E'.f n
    have e : (n : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) := le_antisymm (h1.trans h2) (h3.trans h4)
    exact_mod_cast e
  have hK := bijective_algebraMap_residueField E'.f z hz
  have hfin : Module.finrank k (IsLocalRing.CotangentSpace (E'.A.presheaf.stalk p)) = 2 := by
    rw [← finrank_cotangentSpace_residueField_eq hK, ← hndef, hn2]

  obtain ⟨γ, hγ⟩ := AlgebraicGeometry.Scheme.exists_tangentPoints_equiv_linearMap_cotangentSpace E'.f z hz

  have hτ : ∀ v, IsTangentVector E.L k sk (τ v) := fun v => (hrange _).1 ⟨v, rfl⟩
  let ι : V → TangentPoints E'.f z k := fun v => liftT E sk E' g hg (τ v) (hτ v) hunit
  have hdescι : ∀ v, descT E sk E' g hg (ι v) = τ v := fun v => descT_liftT E sk E' g hg _ _ _
  have hιbij : Function.Bijective ι := by
    constructor
    · intro v w h
      apply hinj
      rw [← hdescι v, ← hdescι w, h]
    · intro w
      have hw : IsTangentVector E.L k sk (descT E sk E' g hg w) :=
        isTangentVector_descT E sk E' g hg (fun t' P Q => hgmul t' P Q) w
      obtain ⟨v, hv⟩ := (hrange _).2 hw
      refine ⟨v, ?_⟩
      apply descT_injective E sk E' g hg
      rw [hdescι, hv]
  have hιadd : ∀ v w, ι (v + w) = mulT E'.L (ι v) (ι w) := by
    intro v w
    apply descT_injective E sk E' g hg
    rw [hdescι, descT_mulT E sk E' g hg (fun t' P Q => hgmul t' P Q), hdescι, hdescι, hadd]
  have hιsmul : ∀ (c : k) (v : V), ι (c • v) = (ι v).map (c • (LinearMap.id : k →ₗ[k] k)) := by
    intro c v
    apply descT_injective E sk E' g hg
    apply Subtype.ext
    rw [hdescι, hsmul, descT_map_smul, hdescι]
  let Φ : V →ₗ[k] (IsLocalRing.CotangentSpace (E'.A.presheaf.stalk p) →ₗ[k] k) :=
    { toFun := fun v => γ k (ι v)
      map_add' := fun v w => by
        show γ k (ι (v + w)) = γ k (ι v) + γ k (ι w)
        rw [hιadd]
        exact gamma_mulT E'.L γ hγ _ _
      map_smul' := fun c v => by
        show γ k (ι (c • v)) = c • γ k (ι v)
        rw [hιsmul]
        exact gamma_map_smul E'.L γ hγ c _ }
  have hΦ : Function.Bijective Φ := (γ k).bijective.comp hιbij
  have e := (LinearEquiv.ofBijective Φ hΦ).finrank_eq
  rw [e]
  change Module.finrank k (Module.Dual k (IsLocalRing.CotangentSpace (E'.A.presheaf.stalk p))) = 2
  rw [Subspace.dual_finrank_eq, hfin]

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_finrank_eq_two_of_range_iff_isTangentVector.D2aTandim"

end S_CerednikDrinfeld_QM_FakeEllipticCurve_finrank_eq_two_of_range_iff_isTangentVector
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_finrank_eq_two_of_range_iff_isTangentVector (solution)
