-- Prove2me | solution 1 for CerednikDrinfeld.QM.finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/28cfc5a0-d1df-5a76-bef1-6d9c322389db

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_AlgHom_exists_cotangent_linearMap_of_fst_eq
import Theorems.Thm_AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TrivSqZeroExt NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

universe u

namespace TangentDimBody

noncomputable section

section SqZero

variable (k : Type u) [CommRing k]
variable (M : Type u) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M]

scoped instance isLocalRing_tsze [IsLocalRing k] : IsLocalRing (TrivSqZeroExt k M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst with h | h
    · exact Or.inl (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr h)
    · refine Or.inr (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ?_)
      rwa [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]

scoped instance isLocalRing_tsze' [IsLocalRing k] : IsLocalRing (CommRingCat.of (TrivSqZeroExt k M)) :=
  isLocalRing_tsze k M

abbrev tS : Spec (CommRingCat.of (TrivSqZeroExt k M)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M)))

abbrev bS : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (TrivSqZeroExt k M)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k M).toRingHom)

theorem bS_tS : bS k M ≫ tS k M = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  rfl

variable {M}
variable {N : Type u} [AddCommGroup N] [Module k N] [Module kᵐᵒᵖ N] [IsCentralScalar k N]
variable {N' : Type u} [AddCommGroup N'] [Module k N'] [Module kᵐᵒᵖ N'] [IsCentralScalar k N']

abbrev mS (φ : M →ₗ[k] N) :
    Spec (CommRingCat.of (TrivSqZeroExt k N)) ⟶ Spec (CommRingCat.of (TrivSqZeroExt k M)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map φ).toRingHom)

theorem mS_tS (φ : M →ₗ[k] N) : mS k φ ≫ tS k M = tS k N := by
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  exact (TrivSqZeroExt.map φ).commutes a

theorem bS_mS (φ : M →ₗ[k] N) : bS k N ≫ mS k φ = bS k M := by
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  exact TrivSqZeroExt.fst_map φ a

theorem mS_id : mS k (LinearMap.id : M →ₗ[k] M) = 𝟙 _ := by
  rw [mS, TrivSqZeroExt.map_id, ← Spec.map_id]
  rfl

theorem mS_comp (φ : M →ₗ[k] N) (ψ : N →ₗ[k] N') : mS k (ψ ∘ₗ φ) = mS k ψ ≫ mS k φ := by
  rw [mS, mS, mS, ← Spec.map_comp, TrivSqZeroExt.map_comp_map]
  rfl

end SqZero

section Tangent

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) (k : Type u) [Field k] (sk : S →+* k)

abbrev γ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom sk)

abbrev e : SchemeHomOver (γ k sk) f := L.one (γ k sk)

variable (M : Type u) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M]

abbrev tA : Spec (CommRingCat.of (TrivSqZeroExt k M)) ⟶ Spec (CommRingCat.of S) := tS k M ≫ γ k sk

theorem bS_tA : bS k M ≫ tA k sk M = γ k sk := by
  rw [← Category.assoc, bS_tS, Category.id_comp]

def TJ : Type u :=
  { t : SchemeHomOver (tA k sk M) f // bS k M ≫ t.1 = (e L k sk).1 }

variable {L k sk M}
variable {N : Type u} [AddCommGroup N] [Module k N] [Module kᵐᵒᵖ N] [IsCentralScalar k N]
variable {N' : Type u} [AddCommGroup N'] [Module k N'] [Module kᵐᵒᵖ N'] [IsCentralScalar k N']

namespace TJ

@[scoped ext] theorem ext {t t' : TJ L k sk M} (h : t.1.1 = t'.1.1) : t = t' := Subtype.ext (Subtype.ext h)

theorem restrict_eq (t : TJ L k sk M) : schemeHomOverComp (bS k M) (bS_tA k sk M) t.1 = e L k sk :=
  Subtype.ext t.2

def one : TJ L k sk M :=
  ⟨L.one _, congrArg Subtype.val (L.one_natural (tA k sk M) (γ k sk) (bS k M) (bS_tA k sk M))⟩

def mul (t t' : TJ L k sk M) : TJ L k sk M :=
  ⟨L.mul _ t.1 t'.1, by
    have h := L.mul_natural (tA k sk M) (γ k sk) (bS k M) (bS_tA k sk M) t.1 t'.1
    rw [t.restrict_eq, t'.restrict_eq, L.mul_one] at h
    exact congrArg Subtype.val h⟩

@[scoped simp] theorem one_val : (one : TJ L k sk M).1 = L.one _ := rfl
@[scoped simp] theorem mul_val (t t' : TJ L k sk M) : (mul t t').1 = L.mul _ t.1 t'.1 := rfl

theorem mul_one (t : TJ L k sk M) : mul t one = t := Subtype.ext (L.mul_one _ _)
theorem one_mul (t : TJ L k sk M) : mul one t = t := Subtype.ext (L.one_mul _ _)

theorem mS_tA (φ : M →ₗ[k] N) : mS k φ ≫ tA k sk M = tA k sk N := by
  rw [← Category.assoc, mS_tS]

def map (φ : M →ₗ[k] N) (t : TJ L k sk M) : TJ L k sk N :=
  ⟨schemeHomOverComp (mS k φ) (mS_tA φ) t.1, by
    change bS k N ≫ mS k φ ≫ t.1.1 = _
    rw [← Category.assoc, bS_mS]
    exact t.2⟩

@[scoped simp] theorem map_val_val (φ : M →ₗ[k] N) (t : TJ L k sk M) : (map φ t).1.1 = mS k φ ≫ t.1.1 := rfl

theorem map_one (φ : M →ₗ[k] N) : map φ (one : TJ L k sk M) = one :=
  Subtype.ext (L.one_natural (tA k sk M) (tA k sk N) (mS k φ) (mS_tA φ))

theorem map_mul (φ : M →ₗ[k] N) (t t' : TJ L k sk M) : map φ (mul t t') = mul (map φ t) (map φ t') :=
  Subtype.ext (L.mul_natural (tA k sk M) (tA k sk N) (mS k φ) (mS_tA φ) _ _)

theorem map_id (t : TJ L k sk M) : map LinearMap.id t = t :=
  TJ.ext (by rw [map_val_val, mS_id, Category.id_comp])

theorem map_comp (φ : M →ₗ[k] N) (ψ : N →ₗ[k] N') (t : TJ L k sk M) :
    map (ψ ∘ₗ φ) t = map ψ (map φ t) :=
  TJ.ext (by rw [map_val_val, map_val_val, map_val_val, mS_comp, Category.assoc])

end TJ
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.TangentDimBody.TJ"

variable (f k sk) in

abbrev J : Scheme.{u} := pullback f (γ k sk)

variable (f k sk) in

abbrev p₁ : J f k sk ⟶ A := pullback.fst f (γ k sk)

variable (f k sk) in

abbrev fJ : J f k sk ⟶ Spec (CommRingCat.of k) := pullback.snd f (γ k sk)

variable (L k sk) in

def eJ : Spec (CommRingCat.of k) ⟶ J f k sk :=
  pullback.lift (e L k sk).1 (𝟙 _) (by rw [(e L k sk).2, Category.id_comp])

theorem eJ_p₁ : eJ L k sk ≫ p₁ f k sk = (e L k sk).1 := pullback.lift_fst _ _ _
theorem eJ_fJ : eJ L k sk ≫ fJ f k sk = 𝟙 _ := pullback.lift_snd _ _ _

variable (L k sk) in

abbrev jpt : ↥(J f k sk) := (eJ L k sk).base (closedPoint k)

scoped instance stalkAlgebra : Algebra k ((J f k sk).presheaf.stalk (jpt L k sk)) :=
  (((J f k sk).presheaf.germ ⊤ (jpt L k sk) trivial).hom.comp
    ((fJ f k sk).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra

theorem algebraMap_stalk (a : k) : algebraMap k ((J f k sk).presheaf.stalk (jpt L k sk)) a =
    ((J f k sk).presheaf.germ ⊤ (jpt L k sk) trivial).hom
      ((fJ f k sk).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) :=
  rfl

variable (L k sk) in

abbrev π : (J f k sk).presheaf.stalk (jpt L k sk) →+* k := (Scheme.stalkClosedPointTo (eJ L k sk)).hom

theorem π_algebraMap (a : k) : π L k sk (algebraMap k _ a) = a := by
  rw [algebraMap_stalk]
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (fJ f k sk).appTop ≫
    (J f k sk).presheaf.germ ⊤ (jpt L k sk) trivial ≫ Scheme.stalkClosedPointTo (eJ L k sk)).hom a = a
  have h1 : (J f k sk).presheaf.germ ⊤ (jpt L k sk) trivial ≫ Scheme.stalkClosedPointTo (eJ L k sk) =
      (eJ L k sk).appTop ≫ (Spec (CommRingCat.of k)).presheaf.germ ⊤ (closedPoint k) trivial ≫
        (stalkClosedPointIso (CommRingCat.of k)).hom := by
    rw [Scheme.stalkClosedPointTo, Scheme.Hom.germ_stalkMap_assoc]
    rfl
  have h2 : (fJ f k sk).appTop ≫ (eJ L k sk).appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, eJ_fJ, Scheme.Hom.id_appTop]
  rw [h1, ← Category.assoc (fJ f k sk).appTop, h2, Category.id_comp, germ_stalkClosedPointIso_hom,
    Iso.inv_hom_id]
  rfl

variable (L k sk) in

def πₐ : (J f k sk).presheaf.stalk (jpt L k sk) →ₐ[k] k :=
  { π L k sk with commutes' := π_algebraMap }

@[scoped simp] theorem πₐ_apply (r : (J f k sk).presheaf.stalk (jpt L k sk)) : πₐ L k sk r = π L k sk r := rfl

variable (L k sk) in

abbrev ωJ : Type u := (RingHom.ker (πₐ L k sk)).Cotangent

section Local

variable {R : Type u} [CommRing R] [IsLocalRing R]

variable (L k sk) in

abbrev Λ₀ (φ : (J f k sk).presheaf.stalk (jpt L k sk) ⟶ CommRingCat.of R) : Spec (CommRingCat.of R) ⟶ J f k sk :=
  Spec.map φ ≫ (J f k sk).fromSpecStalk (jpt L k sk)

theorem Λ₀_injective {φ φ' : (J f k sk).presheaf.stalk (jpt L k sk) ⟶ CommRingCat.of R} [IsLocalHom φ.hom]
    [IsLocalHom φ'.hom] (h : Λ₀ L k sk φ = Λ₀ L k sk φ') : φ = φ' := by
  have h1 : (SpecToEquivOfLocalRing (J f k sk) (CommRingCat.of R)).symm ⟨jpt L k sk, φ, inferInstance⟩ =
      (SpecToEquivOfLocalRing (J f k sk) (CommRingCat.of R)).symm ⟨jpt L k sk, φ', inferInstance⟩ := h
  have h2 := (SpecToEquivOfLocalRing (J f k sk) (CommRingCat.of R)).symm.injective h1
  simp only [Sigma.mk.injEq, heq_eq_eq, Subtype.mk.injEq, true_and] at h2
  exact h2

omit [IsLocalRing R] in
theorem appTop_Λ₀_comp (φ : (J f k sk).presheaf.stalk (jpt L k sk) ⟶ CommRingCat.of R) :
    (Λ₀ L k sk φ ≫ fJ f k sk).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      (fJ f k sk).appTop ≫ (J f k sk).presheaf.germ ⊤ (jpt L k sk) trivial ≫ φ := by
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  simp only [Category.assoc]
  congr 1
  have hle : (homOfLE (le_top : (⊤ : (Spec ((J f k sk).presheaf.stalk (jpt L k sk))).Opens) ≤ ⊤)) = 𝟙 _ := rfl
  rw [hle, op_id, CategoryTheory.Functor.map_id, Category.id_comp, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc]

omit [IsLocalRing R] in
theorem Λ₀_comp_eq_Spec_map (φ : (J f k sk).presheaf.stalk (jpt L k sk) ⟶ CommRingCat.of R) (g : k →+* R)
    (hfg : ∀ a : k, φ.hom (algebraMap k _ a) = g a) :
    Λ₀ L k sk φ ≫ fJ f k sk = Spec.map (CommRingCat.ofHom g) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of R)).hom, appTop_Λ₀_comp, Scheme.ΓSpecIso_naturality,
    ← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of k)).inv, Iso.inv_hom_id_assoc]
  ext a
  exact hfg a

omit [IsLocalRing R] in
theorem apply_algebraMap_of_Λ₀_comp_eq (φ : (J f k sk).presheaf.stalk (jpt L k sk) ⟶ CommRingCat.of R)
    (g : k →+* R) (h : Λ₀ L k sk φ ≫ fJ f k sk = Spec.map (CommRingCat.ofHom g)) (a : k) :
    φ.hom (algebraMap k _ a) = g a := by
  have h1 := appTop_Λ₀_comp (L := L) (k := k) (sk := sk) φ
  rw [h, Scheme.ΓSpecIso_naturality, ← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of k)).inv,
    Iso.inv_hom_id_assoc] at h1
  exact (congrArg (fun ψ : CommRingCat.of k ⟶ CommRingCat.of R => ψ.hom a) h1).symm

end Local
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.TangentDimBody.TJ"

def liftHom (g : ωJ L k sk →ₗ[k] M) : (J f k sk).presheaf.stalk (jpt L k sk) →ₐ[k] TrivSqZeroExt k M :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap (πₐ L k sk) g).choose

theorem fst_liftHom (g : ωJ L k sk →ₗ[k] M) (r : (J f k sk).presheaf.stalk (jpt L k sk)) :
    (liftHom g r).fst = π L k sk r :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap (πₐ L k sk) g).choose_spec.1.1 r

theorem snd_liftHom (g : ωJ L k sk →ₗ[k] M) (a : RingHom.ker (πₐ L k sk)) :
    (liftHom g (a : (J f k sk).presheaf.stalk (jpt L k sk))).snd = g ((RingHom.ker (πₐ L k sk)).toCotangent a) :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap (πₐ L k sk) g).choose_spec.1.2 a

theorem liftHom_unique (g : ωJ L k sk →ₗ[k] M)
    (ψ : (J f k sk).presheaf.stalk (jpt L k sk) →ₐ[k] TrivSqZeroExt k M)
    (h1 : ∀ r, (ψ r).fst = π L k sk r)
    (h2 : ∀ a : RingHom.ker (πₐ L k sk), (ψ (a : (J f k sk).presheaf.stalk (jpt L k sk))).snd =
      g ((RingHom.ker (πₐ L k sk)).toCotangent a)) :
    ψ = liftHom g :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap (πₐ L k sk) g).unique ⟨h1, h2⟩
    (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap (πₐ L k sk) g).choose_spec.1

theorem exists_eq_liftHom (ψ : (J f k sk).presheaf.stalk (jpt L k sk) →ₐ[k] TrivSqZeroExt k M)
    (h1 : ∀ r, (ψ r).fst = π L k sk r) : ∃ g : ωJ L k sk →ₗ[k] M, ψ = liftHom g := by
  obtain ⟨g, hg⟩ := AlgHom.exists_cotangent_linearMap_of_fst_eq (πₐ L k sk) ψ h1
  exact ⟨g, liftHom_unique g ψ h1 hg⟩

theorem liftHom_injective : Function.Injective (liftHom (L := L) (k := k) (sk := sk) (M := M)) := by
  intro g g' hgg'
  apply LinearMap.ext
  intro c
  obtain ⟨a, rfl⟩ := (RingHom.ker (πₐ L k sk)).toCotangent_surjective c
  rw [← snd_liftHom, ← snd_liftHom, hgg']

theorem map_comp_liftHom (φ : M →ₗ[k] N) (g : ωJ L k sk →ₗ[k] M) :
    (TrivSqZeroExt.map φ).comp (liftHom g) = liftHom (φ ∘ₗ g) := by
  refine liftHom_unique _ _ (fun r => ?_) (fun a => ?_)
  · rw [AlgHom.comp_apply, TrivSqZeroExt.fst_map, fst_liftHom]
  · rw [AlgHom.comp_apply, TrivSqZeroExt.snd_map, snd_liftHom, LinearMap.comp_apply]

theorem isLocalHom_of_fst_eq (ψ : (J f k sk).presheaf.stalk (jpt L k sk) →+* TrivSqZeroExt k M)
    (h1 : ∀ r, (ψ r).fst = π L k sk r) : IsLocalHom ψ := by
  constructor
  intro r hr
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, h1] at hr
  exact (isUnit_map_iff (π L k sk) r).mp hr

scoped instance isLocalHom_liftHom (g : ωJ L k sk →ₗ[k] M) :
    IsLocalHom (CommRingCat.ofHom (liftHom g).toRingHom).hom :=
  isLocalHom_of_fst_eq (liftHom g).toRingHom (fst_liftHom g)

theorem isLocalHom_fstHom : IsLocalHom (TrivSqZeroExt.fstHom k k M).toRingHom :=
  ⟨fun _ ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩

scoped instance isLocalHom_fstHom' : IsLocalHom (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k M).toRingHom).hom :=
  isLocalHom_fstHom

theorem Λ₀_liftHom_fJ (g : ωJ L k sk →ₗ[k] M) :
    Λ₀ L k sk (CommRingCat.ofHom (liftHom g).toRingHom) ≫ fJ f k sk = tS k M :=
  Λ₀_comp_eq_Spec_map _ _ (fun a => (liftHom g).commutes a)

theorem bS_Λ₀_liftHom (g : ωJ L k sk →ₗ[k] M) :
    bS k M ≫ Λ₀ L k sk (CommRingCat.ofHom (liftHom g).toRingHom) = eJ L k sk := by
  rw [bS, ← Spec.map_comp_assoc]
  convert Scheme.Spec_stalkClosedPointTo_fromSpecStalk (eJ L k sk) using 3
  exact CommRingCat.hom_ext (RingHom.ext fun r => fst_liftHom g r)

def pointOf (g : ωJ L k sk →ₗ[k] M) : TJ L k sk M :=
  ⟨⟨Λ₀ L k sk (CommRingCat.ofHom (liftHom g).toRingHom) ≫ p₁ f k sk, by
      rw [Category.assoc, pullback.condition, ← Category.assoc, Λ₀_liftHom_fJ]⟩, by
    change bS k M ≫ Λ₀ L k sk (CommRingCat.ofHom (liftHom g).toRingHom) ≫ p₁ f k sk = _
    rw [← Category.assoc, bS_Λ₀_liftHom, eJ_p₁]⟩

@[scoped simp] theorem pointOf_val_val (g : ωJ L k sk →ₗ[k] M) :
    (pointOf g).1.1 = Λ₀ L k sk (CommRingCat.ofHom (liftHom g).toRingHom) ≫ p₁ f k sk := rfl

theorem pointOf_injective : Function.Injective (pointOf (L := L) (k := k) (sk := sk) (M := M)) := by
  intro g g' hgg'
  have h : (pointOf g).1.1 = (pointOf g').1.1 := by rw [hgg']
  rw [pointOf_val_val, pointOf_val_val] at h
  have h' : Λ₀ L k sk (CommRingCat.ofHom (liftHom g).toRingHom) =
      Λ₀ L k sk (CommRingCat.ofHom (liftHom g').toRingHom) :=
    pullback.hom_ext h (by rw [Λ₀_liftHom_fJ, Λ₀_liftHom_fJ])
  have h2 := Λ₀_injective h'
  apply liftHom_injective
  apply AlgHom.ext
  intro r
  exact congrArg (fun ψ : (J f k sk).presheaf.stalk (jpt L k sk) ⟶ CommRingCat.of (TrivSqZeroExt k M) =>
    ψ.hom r) h2

theorem pointOf_map (φ : M →ₗ[k] N) (g : ωJ L k sk →ₗ[k] M) :
    pointOf (φ ∘ₗ g) = TJ.map φ (pointOf g) := by
  apply TJ.ext
  rw [pointOf_val_val, TJ.map_val_val, pointOf_val_val, mS, ← Category.assoc, ← Spec.map_comp_assoc,
    ← map_comp_liftHom]
  rfl

def liftJ (t : TJ L k sk M) : Spec (CommRingCat.of (TrivSqZeroExt k M)) ⟶ J f k sk :=
  pullback.lift t.1.1 (tS k M) t.1.2

theorem liftJ_p₁ (t : TJ L k sk M) : liftJ t ≫ p₁ f k sk = t.1.1 := pullback.lift_fst _ _ _
theorem liftJ_fJ (t : TJ L k sk M) : liftJ t ≫ fJ f k sk = tS k M := pullback.lift_snd _ _ _

theorem bS_liftJ (t : TJ L k sk M) : bS k M ≫ liftJ t = eJ L k sk := by
  apply pullback.hom_ext
  · rw [Category.assoc, liftJ_p₁, eJ_p₁, t.2]
  · rw [Category.assoc, liftJ_fJ, eJ_fJ, bS_tS]

theorem pointOf_surjective : Function.Surjective (pointOf (L := L) (k := k) (sk := sk) (M := M)) := by
  intro t
  obtain ⟨⟨q, φ₀, hφ₀⟩, ht⟩ :
      ∃ z, (SpecToEquivOfLocalRing (J f k sk) (CommRingCat.of (TrivSqZeroExt k M))).symm z = liftJ t :=
    (SpecToEquivOfLocalRing (J f k sk) (CommRingCat.of (TrivSqZeroExt k M))).symm.surjective (liftJ t)
  have hq : q = jpt L k sk := by
    have h1 : ((SpecToEquivOfLocalRing (J f k sk) (CommRingCat.of (TrivSqZeroExt k M))).symm
        ⟨q, φ₀, hφ₀⟩).base (closedPoint (TrivSqZeroExt k M)) = q := by
      rw [SpecToEquivOfLocalRing_symm_apply, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply,
        Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
    rw [← h1, ht]
    have h2 : (bS k M).base (closedPoint k) = closedPoint (TrivSqZeroExt k M) := Spec_closedPoint
    rw [← h2, ← Scheme.Hom.comp_apply, bS_liftJ]
  subst hq
  have ht' : liftJ t = Λ₀ L k sk φ₀ := ht.symm
  have hcomm : ∀ a : k, φ₀.hom (algebraMap k _ a) = algebraMap k (TrivSqZeroExt k M) a :=
    apply_algebraMap_of_Λ₀_comp_eq φ₀ _ (by rw [← ht']; exact liftJ_fJ t)
  let ψ : (J f k sk).presheaf.stalk (jpt L k sk) →ₐ[k] TrivSqZeroExt k M := { φ₀.hom with commutes' := hcomm }
  have hfst : ∀ r, (ψ r).fst = π L k sk r := by
    haveI := hφ₀
    haveI : IsLocalHom (φ₀ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom k k M).toRingHom).hom := by
      change IsLocalHom ((TrivSqZeroExt.fstHom k k M).toRingHom.comp φ₀.hom)
      haveI := isLocalHom_fstHom (k := k) (M := M)
      exact RingHom.isLocalHom_comp _ _
    have h1 : Λ₀ L k sk (φ₀ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom k k M).toRingHom) =
        Λ₀ L k sk (Scheme.stalkClosedPointTo (eJ L k sk)) := by
      rw [Λ₀, Λ₀, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, Spec.map_comp, Category.assoc]
      change bS k M ≫ Λ₀ L k sk φ₀ = eJ L k sk
      rw [← ht', bS_liftJ]
    have h2 := Λ₀_injective h1
    intro r
    exact congrArg (fun χ : (J f k sk).presheaf.stalk (jpt L k sk) ⟶ CommRingCat.of k => χ.hom r) h2
  obtain ⟨g, hg⟩ := exists_eq_liftHom ψ hfst
  refine ⟨g, TJ.ext ?_⟩
  rw [pointOf_val_val, ← liftJ_p₁ t, ht', ← hg]
  rfl

variable (L k sk M) in

def γJ : TJ L k sk M ≃ (ωJ L k sk →ₗ[k] M) :=
  (Equiv.ofBijective pointOf ⟨pointOf_injective, pointOf_surjective⟩).symm

theorem γJ_symm_apply (g : ωJ L k sk →ₗ[k] M) : (γJ L k sk M).symm g = pointOf g := rfl

theorem γJ_pointOf (g : ωJ L k sk →ₗ[k] M) : γJ L k sk M (pointOf g) = g :=
  (γJ L k sk M).apply_symm_apply g

theorem γJ_map (φ : M →ₗ[k] N) (t : TJ L k sk M) : γJ L k sk N (TJ.map φ t) = φ ∘ₗ γJ L k sk M t := by
  obtain ⟨g, rfl⟩ := (γJ L k sk M).symm.surjective t
  rw [γJ_symm_apply, ← pointOf_map, γJ_pointOf, γJ_pointOf]

theorem TJ_punit_eq_one (t : TJ L k sk PUnit.{u + 1}) : t = TJ.one :=
  (γJ L k sk PUnit.{u + 1}).injective (Subsingleton.elim _ _)

theorem TJ_map_zero (t : TJ L k sk M) : TJ.map (0 : M →ₗ[k] N) t = TJ.one := by
  have h0 : (0 : M →ₗ[k] N) = (0 : PUnit.{u + 1} →ₗ[k] N) ∘ₗ (0 : M →ₗ[k] PUnit.{u + 1}) := rfl
  rw [h0, TJ.map_comp, TJ_punit_eq_one (TJ.map 0 t), TJ.map_one]

theorem γJ_mul (t t' : TJ L k sk M) : γJ L k sk M (TJ.mul t t') = γJ L k sk M t + γJ L k sk M t' := by
  let z : TJ L k sk (M × M) := TJ.mul (TJ.map (LinearMap.inl k M M) t) (TJ.map (LinearMap.inr k M M) t')
  have h1 : TJ.map (LinearMap.fst k M M) z = t := by
    change TJ.map _ (TJ.mul _ _) = t
    rw [TJ.map_mul, ← TJ.map_comp, ← TJ.map_comp, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr,
      TJ.map_id, TJ_map_zero, TJ.mul_one]
  have h2 : TJ.map (LinearMap.snd k M M) z = t' := by
    change TJ.map _ (TJ.mul _ _) = t'
    rw [TJ.map_mul, ← TJ.map_comp, ← TJ.map_comp, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr,
      TJ.map_id, TJ_map_zero, TJ.one_mul]
  have h3 : TJ.map (LinearMap.fst k M M + LinearMap.snd k M M) z = TJ.mul t t' := by
    change TJ.map _ (TJ.mul _ _) = _
    have e1 : (LinearMap.fst k M M + LinearMap.snd k M M) ∘ₗ LinearMap.inl k M M = LinearMap.id := by
      rw [LinearMap.add_comp, LinearMap.fst_comp_inl, LinearMap.snd_comp_inl, add_zero]
    have e2 : (LinearMap.fst k M M + LinearMap.snd k M M) ∘ₗ LinearMap.inr k M M = LinearMap.id := by
      rw [LinearMap.add_comp, LinearMap.fst_comp_inr, LinearMap.snd_comp_inr, zero_add]
    rw [TJ.map_mul, ← TJ.map_comp, ← TJ.map_comp, e1, e2, TJ.map_id, TJ.map_id]
  have k1 : LinearMap.fst k M M ∘ₗ γJ L k sk (M × M) z = γJ L k sk M t := by rw [← γJ_map, h1]
  have k2 : LinearMap.snd k M M ∘ₗ γJ L k sk (M × M) z = γJ L k sk M t' := by rw [← γJ_map, h2]
  rw [← h3, γJ_map, LinearMap.add_comp, k1, k2]

section Free

open TensorProduct KaehlerDifferential

theorem fJ_jpt : (fJ f k sk).base (jpt L k sk) = closedPoint k := by
  change (eJ L k sk ≫ fJ f k sk).base (closedPoint k) = closedPoint k
  rw [eJ_fJ]
  rfl

variable (L k sk) in

theorem nonempty_ωJ_equiv (n : ℕ) [SmoothOfRelativeDimension n f] : Nonempty (ωJ L k sk ≃ₗ[k] (Fin n → k)) := by
  haveI : SmoothOfRelativeDimension n (fJ f k sk) := by
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange n
    exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ inferInstance
  obtain ⟨U, hU, V, hV, hjV, hle, hsm⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := fJ f k sk) (jpt L k sk)

  have hUtop : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp (by rw [← fJ_jpt (L := L)]; exact hle hjV)
  subst hUtop

  let O := (J f k sk).presheaf.stalk (jpt L k sk)
  let B := Γ(J f k sk, V)
  let ρ : k →+* B := ((fJ f k sk).appLE ⊤ V hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  letI algRB : Algebra k B := ρ.toAlgebra
  haveI hB : Algebra.IsStandardSmoothOfRelativeDimension n k B :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 ((fJ f k sk).appLE ⊤ V hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv hsm
  haveI : Algebra.IsStandardSmooth k B := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n

  letI algBO : Algebra B O := TopCat.Presheaf.algebra_section_stalk (J f k sk).presheaf ⟨jpt L k sk, hjV⟩
  haveI : IsLocalization.AtPrime O (hV.primeIdealOf ⟨jpt L k sk, hjV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨jpt L k sk, hjV⟩
  haveI : Algebra.FormallyEtale B O :=
    Algebra.FormallyEtale.of_isLocalization (hV.primeIdealOf ⟨jpt L k sk, hjV⟩).asIdeal.primeCompl
  haveI : IsScalarTower k B O := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change ((J f k sk).presheaf.germ ⊤ (jpt L k sk) trivial).hom ((fJ f k sk).appTop.hom _) =
      ((J f k sk).presheaf.germ V (jpt L k sk) hjV).hom
        (((fJ f k sk).app ⊤ ≫ (J f k sk).presheaf.map (homOfLE hle).op).hom _)
    rw [CommRingCat.comp_apply, ← CommRingCat.comp_apply _ ((J f k sk).presheaf.germ V (jpt L k sk) hjV),
      TopCat.Presheaf.germ_res]
    rfl
  haveI : Nontrivial B := (algebraMap B O).domain_nontrivial

  let EΩ : O ⊗[B] Ω[B⁄k] ≃ₗ[O] Ω[O⁄k] := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k B O
  haveI : Module.Free O Ω[O⁄k] := Module.Free.of_equiv EΩ
  have hrkB : Module.rank B Ω[B⁄k] = n := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  have hrkO : Module.rank O Ω[O⁄k] = n := by
    rw [← EΩ.rank_eq, Module.rank_baseChange, hrkB]
    simp

  letI algOR : Algebra O k := (πₐ L k sk).toRingHom.toAlgebra
  haveI : IsScalarTower k O k := IsScalarTower.of_algebraMap_eq' (πₐ L k sk).comp_algebraMap.symm
  have hsurj : Function.Surjective (algebraMap O k) := fun r => ⟨algebraMap k O r, π_algebraMap r⟩
  have hexact := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k O k hsurj
  haveI : Subsingleton Ω[k⁄k] := KaehlerDifferential.subsingleton_of_surjective k k Function.surjective_id
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := k) (P := O) (S := k) hsurj).symm
    ⟨Algebra.ofId k _, Subsingleton.elim _ _⟩
  have hbij : Function.Bijective (kerCotangentToTensor k O k) := by
    refine ⟨fun x y hxy => ?_, fun z => (hexact z).mp (Subsingleton.elim _ _)⟩
    have := congrArg l hxy
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hl] at this
  let E1 : ωJ L k sk ≃ₗ[O] k ⊗[O] Ω[O⁄k] := LinearEquiv.ofBijective _ hbij

  have hrkR : Module.rank k (k ⊗[O] Ω[O⁄k]) = Module.rank k (Fin n → k) := by
    rw [Module.rank_baseChange, hrkO, rank_fin_fun]
    simp
  obtain ⟨E2⟩ := nonempty_linearEquiv_of_rank_eq hrkR
  exact ⟨(E1.restrictScalars k).trans E2⟩

end Free
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.TangentDimBody.TJ"

theorem tangentBase_eq : tangentBase k sk = tA k sk k := by
  rw [tangentBase, tA, tS, γ, ← Spec.map_comp]
  rfl

def castBase {T : Scheme.{u}} {a b : T ⟶ Spec (CommRingCat.of S)} (h : a = b) (P : SchemeHomOver a f) :
    SchemeHomOver b f :=
  ⟨P.1, by rw [← h]; exact P.2⟩

@[scoped simp] theorem castBase_coe {T : Scheme.{u}} {a b : T ⟶ Spec (CommRingCat.of S)} (h : a = b)
    (P : SchemeHomOver a f) : (castBase h P).1 = P.1 := rfl

theorem castBase_mul {T : Scheme.{u}} {a b : T ⟶ Spec (CommRingCat.of S)} (h : a = b) (P Q : SchemeHomOver a f) :
    castBase h (L.mul a P Q) = L.mul b (castBase h P) (castBase h Q) := by
  subst h; rfl

theorem castBase_injective {T : Scheme.{u}} {a b : T ⟶ Spec (CommRingCat.of S)} (h : a = b) :
    Function.Injective (castBase (f := f) h) := by
  subst h; intro P Q hPQ; exact hPQ

theorem castBase_surjective {T : Scheme.{u}} {a b : T ⟶ Spec (CommRingCat.of S)} (h : a = b) :
    Function.Surjective (castBase (f := f) h) := by
  subst h; intro P; exact ⟨P, rfl⟩

theorem toTJ_prop (P : SchemeHomOver (tangentBase k sk) f) (hP : IsTangentVector L k sk P) :
    bS k k ≫ (castBase (f := f) tangentBase_eq P).1 = (e L k sk).1 := by
  rw [castBase_coe]
  have h : tangentZero k ≫ P.1 = (L.one (geomPoint k sk)).1 := hP
  exact h

def toTJ (P : SchemeHomOver (tangentBase k sk) f) (hP : IsTangentVector L k sk P) : TJ L k sk k :=
  ⟨castBase tangentBase_eq P, toTJ_prop P hP⟩

@[scoped simp] theorem toTJ_val (P : SchemeHomOver (tangentBase k sk) f) (hP : IsTangentVector L k sk P) :
    (toTJ P hP).1 = castBase tangentBase_eq P := rfl

theorem main (n : ℕ) [SmoothOfRelativeDimension n f]
    (V : Type u) [AddCommGroup V] [Module k V] (τ : V → SchemeHomOver (tangentBase k sk) f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P)
    (hadd : ∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) :
    Module.finrank k V = n := by
  have hτ : ∀ v, IsTangentVector L k sk (τ v) := fun v => (hrange (τ v)).mp ⟨v, rfl⟩

  let β : V → (ωJ L k sk →ₗ[k] k) := fun v => γJ L k sk k (toTJ (τ v) (hτ v))
  have hβ_add : ∀ v w, β (v + w) = β v + β w := by
    intro v w
    change γJ L k sk k (toTJ (τ (v + w)) (hτ _)) = _
    have h : toTJ (τ (v + w)) (hτ _) = TJ.mul (toTJ (τ v) (hτ v)) (toTJ (τ w) (hτ w)) := by
      apply Subtype.ext
      rw [toTJ_val, hadd, castBase_mul]
      rfl
    rw [h, γJ_mul]
  have hβ_smul : ∀ (c : k) (v : V), β (c • v) = c • β v := by
    intro c v
    change γJ L k sk k (toTJ (τ (c • v)) (hτ _)) = _
    have h : toTJ (τ (c • v)) (hτ _) = TJ.map (c • LinearMap.id) (toTJ (τ v) (hτ v)) := by
      apply TJ.ext
      rw [TJ.map_val_val, toTJ_val, toTJ_val, castBase_coe, castBase_coe, hsmul]
      rfl
    rw [h, γJ_map]
    ext x
    rfl
  let βₗ : V →ₗ[k] (ωJ L k sk →ₗ[k] k) := { toFun := β, map_add' := hβ_add, map_smul' := hβ_smul }
  have hβ_inj : Function.Injective βₗ := by
    intro v w hvw
    have h1 : toTJ (τ v) (hτ v) = toTJ (τ w) (hτ w) := (γJ L k sk k).injective hvw
    have h2 : castBase tangentBase_eq (τ v) = castBase tangentBase_eq (τ w) := congrArg Subtype.val h1
    exact hinj (castBase_injective _ h2)
  have hβ_surj : Function.Surjective βₗ := by
    intro g
    obtain ⟨t, rfl⟩ := (γJ L k sk k).surjective g
    obtain ⟨P, hP⟩ := castBase_surjective (f := f) tangentBase_eq t.1
    have hPt : IsTangentVector L k sk P := by
      change bS k k ≫ P.1 = _
      rw [← castBase_coe tangentBase_eq P, hP]
      exact t.2
    obtain ⟨v, rfl⟩ := (hrange P).mpr hPt
    refine ⟨v, ?_⟩
    change γJ L k sk k (toTJ (τ v) (hτ v)) = γJ L k sk k t
    congr 1
    exact Subtype.ext hP
  let E : V ≃ₗ[k] (ωJ L k sk →ₗ[k] k) := LinearEquiv.ofBijective βₗ ⟨hβ_inj, hβ_surj⟩
  obtain ⟨Eω⟩ := nonempty_ωJ_equiv L k sk n
  let E' : (ωJ L k sk →ₗ[k] k) ≃ₗ[k] ((Fin n → k) →ₗ[k] k) := Eω.congrLeft k k
  rw [E.finrank_eq, E'.finrank_eq, Module.finrank_linearMap, Module.finrank_fin_fun, Module.finrank_self,
    mul_one]

end Tangent
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.TangentDimBody.TJ"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.TangentDimBody.TJ"

end TangentDimBody
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.TangentDimBody.TJ P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.TangentDimBody"

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (k : Type u) [Field k] (sk : S →+* k)
    (V : Type u) [AddCommGroup V] [Module k V] (τ : V → SchemeHomOver (tangentBase k sk) f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P)
    (hadd : ∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) :
    Module.finrank k V = n :=
  TangentDimBody.main (L := L) (k := k) (sk := sk) n V τ hinj hrange hadd hsmul

end S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension
end P2MW
export P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension (solution)
