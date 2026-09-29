-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/223cc34e-6e55-5436-ba5f-6f2a88162f6a

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_existsUnique_extension_hom_of_genericFibre
import Theorems.Thm_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle.GoodReductionJacobian"
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle.CerednikDrinfeld.QM"
open scoped Quaternion

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.baseChangePointToBase RelativeGroupLaw.baseChangePointToBase_coe RelativeGroupLaw.baseChangePointOfBase_coe RelativeGroupLaw.baseChangePointEquiv RelativeGroupLaw.baseChange_mul RelativeGroupLaw.baseChangePointToBase_mul RelativeGroupLaw.genericFibreStr AbelianSchemePropertyBundle.existsUnique_extension_hom_of_genericFibre"
namespace AbelianSchemePropertyBundle
p2m_export "GoodReductionJacobian.AbelianSchemePropertyBundle" "smooth existsUnique_extension_hom_of_genericFibre"
namespace RingActionExtension
p2m_open "GoodReductionJacobian.AbelianSchemePropertyBundle GoodReductionJacobian"

section Plumbing

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem baseChangePointToBase_genericFibreRestrict (φ : SchemeHomOver f f) :
    RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) (genericFibreRestrict R K f f φ) =
      GoodReductionJacobian.schemeHomOverComp (pullback.fst f (specGenericFibreInclusion R K))
        pullback.condition φ := by
  apply Subtype.ext
  rw [RelativeGroupLaw.baseChangePointToBase_coe, GoodReductionJacobian.schemeHomOverComp_coe]
  exact genericFibreRestrict_coe_comp_fst f f φ

theorem genericFibreRestrict_mul (LA : RelativeGroupLaw R f) (φ ψ : SchemeHomOver f f) :
    genericFibreRestrict R K f f (LA.mul f φ ψ) =
      (LA.genericFibre K).mul (RelativeGroupLaw.genericFibreStr K f)
        (genericFibreRestrict R K f f φ) (genericFibreRestrict R K f f ψ) := by
  rw [RelativeGroupLaw.baseChange_mul, baseChangePointToBase_genericFibreRestrict,
    baseChangePointToBase_genericFibreRestrict,
    ← LA.mul_natural f _ (pullback.fst f (specGenericFibreInclusion R K)) pullback.condition φ ψ]
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst,
      GoodReductionJacobian.schemeHomOverComp_coe]
    exact genericFibreRestrict_coe_comp_fst f f _
  · rw [RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd]
    exact genericFibreRestrict_coe_comp_snd f f _

theorem schemeHomOverComp_mul (LA : RelativeGroupLaw R f) (φ ψ : SchemeHomOver f f)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s f) :
    NeronModelInfra.schemeHomOverComp x (LA.mul f φ ψ) =
      LA.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp x ψ) :=
  LA.mul_natural f s x.1 x.2 φ ψ

theorem schemeHomOverComp_schemeHomOverId {S : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver s f) : NeronModelInfra.schemeHomOverComp x (schemeHomOverId f) = x := by
  apply Subtype.ext
  simp

end Plumbing

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem main (hA : AbelianSchemePropertyBundle R f) (LA : RelativeGroupLaw R f)
    {ι : Type v}
    (u : ι → SchemeHomOver (RelativeGroupLaw.genericFibreStr K f) (RelativeGroupLaw.genericFibreStr K f))
    (hu : ∀ (i : ι) {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver s (RelativeGroupLaw.genericFibreStr K f)),
        NeronModelInfra.schemeHomOverComp ((LA.genericFibre K).mul s x y) (u i) =
          (LA.genericFibre K).mul s (NeronModelInfra.schemeHomOverComp x (u i))
            (NeronModelInfra.schemeHomOverComp y (u i))) :
    ∃ v : ι → SchemeHomOver f f,
      (∀ i, genericFibreRestrict R K f f (v i) = u i) ∧
      (∀ (i : ι) {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
        NeronModelInfra.schemeHomOverComp (LA.mul s x y) (v i) =
          LA.mul s (NeronModelInfra.schemeHomOverComp x (v i)) (NeronModelInfra.schemeHomOverComp y (v i))) ∧
      (∀ (i : ι) (φ : SchemeHomOver f f), genericFibreRestrict R K f f φ = u i → φ = v i) ∧
      (∀ i, u i = schemeHomOverId (RelativeGroupLaw.genericFibreStr K f) → v i = schemeHomOverId f) ∧
      (∀ i j k, u k = NeronModelInfra.schemeHomOverComp (u i) (u j) →
        v k = NeronModelInfra.schemeHomOverComp (v i) (v j)) ∧
      (∀ i j k,
        (∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K))
            (x : SchemeHomOver s (RelativeGroupLaw.genericFibreStr K f)),
          NeronModelInfra.schemeHomOverComp x (u k) =
            (LA.genericFibre K).mul s (NeronModelInfra.schemeHomOverComp x (u i))
              (NeronModelInfra.schemeHomOverComp x (u j))) →
        ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s f),
          NeronModelInfra.schemeHomOverComp x (v k) =
            LA.mul s (NeronModelInfra.schemeHomOverComp x (v i)) (NeronModelInfra.schemeHomOverComp x (v j))) := by

  have hN : NeronModelPropertyBundle R K f := NeronModelPropertyBundle.of_abelianSchemePropertyBundle R K hA
  have hinj : Function.Injective (genericFibreRestrict R K f f) := hN.endRestrict_bijective.injective
  haveI : Smooth f := hA.smooth

  have hex : ∀ i, ∃! φ : SchemeHomOver f f,
      genericFibreRestrict R K f f φ = u i ∧
      ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
        NeronModelInfra.schemeHomOverComp (LA.mul s x y) φ =
          LA.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ) :=
    fun i => AbelianSchemePropertyBundle.existsUnique_extension_hom_of_genericFibre R K hA LA LA (u i) (hu i)
  choose v hv _huniq using hex
  refine ⟨v, fun i => (hv i).1, fun i S s x y => (hv i).2 s x y, ?_, ?_, ?_, ?_⟩
  ·
    intro i φ hφ
    exact hinj (hφ.trans (hv i).1.symm)
  ·
    intro i hi
    apply hinj
    rw [(hv i).1, hi, genericFibreRestrict_schemeHomOverId]
  ·
    intro i j k hk
    apply hinj
    rw [(hv k).1, hk, genericFibreRestrict_endComp, (hv i).1, (hv j).1]
  ·
    intro i j k hk S s x
    have hvk : v k = LA.mul f (v i) (v j) := by
      apply hinj
      rw [genericFibreRestrict_mul, (hv i).1, (hv j).1, (hv k).1]
      have h := hk (RelativeGroupLaw.genericFibreStr K f) (schemeHomOverId _)
      simpa only [schemeHomOverComp_id_left] using h
    rw [hvk]
    exact schemeHomOverComp_mul LA (v i) (v j) s x

end Main

end GoodReductionJacobian.AbelianSchemePropertyBundle.RingActionExtension

namespace CerednikDrinfeld
namespace QM
p2m_export "CerednikDrinfeld.QM" "mapPt_coe pushPt FakeEllipticCurve FakeEllipticCurve.IsPullback"
namespace ActionExtension
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

open GoodReductionJacobian.AbelianSchemePropertyBundle.RingActionExtension

section Transport

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
variable {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)}
variable {P : Scheme.{u}} {fP : P ⟶ Spec (CommRingCat.of K)}
variable {g : P ⟶ 𝒜} (hg : IsPullback g fP f (specGenericFibreInclusion R K))

noncomputable def ofP {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of K)} (w : SchemeHomOver t' fP) :
    SchemeHomOver t' (RelativeGroupLaw.genericFibreStr K f) :=
  ⟨w.1 ≫ hg.isoPullback.hom, by
    rw [Category.assoc]
    show w.1 ≫ hg.isoPullback.hom ≫ pullback.snd f (specGenericFibreInclusion R K) = t'
    rw [hg.isoPullback_hom_snd, w.2]⟩

noncomputable def toP {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of K)}
    (w : SchemeHomOver t' (RelativeGroupLaw.genericFibreStr K f)) : SchemeHomOver t' fP :=
  ⟨w.1 ≫ hg.isoPullback.inv, by rw [Category.assoc, hg.isoPullback_inv_snd]; exact w.2⟩

@[scoped simp] theorem ofP_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of K)} (w : SchemeHomOver t' fP) :
    (ofP hg w).1 = w.1 ≫ hg.isoPullback.hom := rfl

@[scoped simp] theorem toP_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of K)}
    (w : SchemeHomOver t' (RelativeGroupLaw.genericFibreStr K f)) :
    (toP hg w).1 = w.1 ≫ hg.isoPullback.inv := rfl

@[scoped simp] theorem toP_ofP {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of K)} (w : SchemeHomOver t' fP) :
    toP hg (ofP hg w) = w := by
  apply Subtype.ext
  rw [toP_coe, ofP_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id]

@[scoped simp] theorem ofP_toP {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of K)}
    (w : SchemeHomOver t' (RelativeGroupLaw.genericFibreStr K f)) : ofP hg (toP hg w) = w := by
  apply Subtype.ext
  rw [ofP_coe, toP_coe, Category.assoc, Iso.inv_hom_id, Category.comp_id]

def overG {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of K)} (w : SchemeHomOver t' fP) :
    SchemeHomOver (t' ≫ specGenericFibreInclusion R K) f :=
  ⟨w.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, w.2]⟩

theorem baseChangePointToBase_ofP {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of K)}
    (w : SchemeHomOver t' fP) :
    RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) (ofP hg w) = overG hg w := by
  apply Subtype.ext
  rw [RelativeGroupLaw.baseChangePointToBase_coe, ofP_coe, Category.assoc, hg.isoPullback_hom_fst]
  rfl

variable (L : RelativeGroupLaw R f) (LP : RelativeGroupLaw K fP)

def SquareHom : Prop :=
  ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' fP),
    (LP.mul t' x y).1 ≫ g = (L.mul (t' ≫ specGenericFibreInclusion R K) (overG hg x) (overG hg y)).1

variable {L LP}

theorem ofP_mul (hmul : SquareHom hg L LP) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t' fP) :
    ofP hg (LP.mul t' x y) = (L.genericFibre K).mul t' (ofP hg x) (ofP hg y) := by
  apply (RelativeGroupLaw.baseChangePointEquiv (specGenericFibreInclusion R K) t').injective
  show RelativeGroupLaw.baseChangePointToBase _ _ = RelativeGroupLaw.baseChangePointToBase _ _
  rw [RelativeGroupLaw.baseChangePointToBase_mul, baseChangePointToBase_ofP, baseChangePointToBase_ofP,
    baseChangePointToBase_ofP]
  apply Subtype.ext
  exact hmul t' x y

theorem toP_mul (hmul : SquareHom hg L LP) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t' (RelativeGroupLaw.genericFibreStr K f)) :
    toP hg ((L.genericFibre K).mul t' x y) = LP.mul t' (toP hg x) (toP hg y) := by
  have h := ofP_mul hg hmul t' (toP hg x) (toP hg y)
  rw [ofP_toP, ofP_toP] at h
  rw [← h, toP_ofP]

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
variable (act : ↥Λ → (P ⟶ P)) (act_over : ∀ x : ↥Λ, act x ≫ fP = fP)

noncomputable def uAct (x : ↥Λ) :
    SchemeHomOver (RelativeGroupLaw.genericFibreStr K f) (RelativeGroupLaw.genericFibreStr K f) :=
  ⟨hg.isoPullback.inv ≫ act x ≫ hg.isoPullback.hom, by
    show (hg.isoPullback.inv ≫ act x ≫ hg.isoPullback.hom) ≫ pullback.snd f (specGenericFibreInclusion R K) =
      pullback.snd f (specGenericFibreInclusion R K)
    rw [Category.assoc, Category.assoc, hg.isoPullback_hom_snd, act_over, hg.isoPullback_inv_snd]⟩

@[scoped simp] theorem uAct_coe (x : ↥Λ) :
    (uAct hg act act_over x).1 = hg.isoPullback.inv ≫ act x ≫ hg.isoPullback.hom := rfl

theorem schemeHomOverComp_uAct {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of K)}
    (w : SchemeHomOver t' (RelativeGroupLaw.genericFibreStr K f)) (x : ↥Λ) :
    NeronModelInfra.schemeHomOverComp w (uAct hg act act_over x) =
      ofP hg (pushPt (act x) (act_over x) (toP hg w)) := by
  apply Subtype.ext
  simp only [NeronModelInfra.schemeHomOverComp_coe, uAct_coe, ofP_coe, mapPt_coe, toP_coe, Category.assoc]

variable {act act_over}

theorem uAct_hom (hmul : SquareHom hg L LP)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (u v : SchemeHomOver t fP),
      pushPt (act x) (act_over x) (LP.mul t u v) =
        LP.mul t (pushPt (act x) (act_over x) u) (pushPt (act x) (act_over x) v))
    (x : ↥Λ) {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K))
    (w₁ w₂ : SchemeHomOver s (RelativeGroupLaw.genericFibreStr K f)) :
    NeronModelInfra.schemeHomOverComp ((L.genericFibre K).mul s w₁ w₂) (uAct hg act act_over x) =
      (L.genericFibre K).mul s (NeronModelInfra.schemeHomOverComp w₁ (uAct hg act act_over x))
        (NeronModelInfra.schemeHomOverComp w₂ (uAct hg act act_over x)) := by
  rw [schemeHomOverComp_uAct, schemeHomOverComp_uAct, schemeHomOverComp_uAct, toP_mul hg hmul, act_hom,
    ofP_mul hg hmul]

theorem uAct_add (hmul : SquareHom hg L LP)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (u : SchemeHomOver t fP),
      pushPt (act (x + y)) (act_over (x + y)) u =
        LP.mul t (pushPt (act x) (act_over x) u) (pushPt (act y) (act_over y) u))
    (x y : ↥Λ) {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K))
    (w : SchemeHomOver s (RelativeGroupLaw.genericFibreStr K f)) :
    NeronModelInfra.schemeHomOverComp w (uAct hg act act_over (x + y)) =
      (L.genericFibre K).mul s (NeronModelInfra.schemeHomOverComp w (uAct hg act act_over x))
        (NeronModelInfra.schemeHomOverComp w (uAct hg act act_over y)) := by
  rw [schemeHomOverComp_uAct, schemeHomOverComp_uAct, schemeHomOverComp_uAct, act_add, ofP_mul hg hmul]

theorem uAct_one (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 P) (h : (1 : ℍ[ℚ, a, b]) ∈ Λ) :
    uAct hg act act_over ⟨1, h⟩ = schemeHomOverId (RelativeGroupLaw.genericFibreStr K f) := by
  apply Subtype.ext
  rw [uAct_coe, act_one h, Category.id_comp, Iso.inv_hom_id, schemeHomOverId_coe]

theorem uAct_mul
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    uAct hg act act_over ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ =
      NeronModelInfra.schemeHomOverComp (uAct hg act act_over y) (uAct hg act act_over x) := by
  apply Subtype.ext
  simp only [uAct_coe, NeronModelInfra.schemeHomOverComp_coe, act_mul x y h, Category.assoc,
    Iso.hom_inv_id_assoc]

theorem pushPt_eq_schemeHomOverComp {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (φ : SchemeHomOver f f) (w : SchemeHomOver t f) :
    pushPt φ.1 φ.2 w = NeronModelInfra.schemeHomOverComp w φ := rfl

end Transport

section Main

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
variable {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)}
variable {P : Scheme.{u}} {fP : P ⟶ Spec (CommRingCat.of K)}

theorem fec_main (L : RelativeGroupLaw R f) (h𝒜 : AbelianSchemePropertyBundle R f) (LP : RelativeGroupLaw K fP)
    (g : P ⟶ 𝒜) (hg : IsPullback g fP f (specGenericFibreInclusion R K))
    (hg_mul : SquareHom hg L LP)
    (act : ↥Λ → (P ⟶ P)) (act_over : ∀ x : ↥Λ, act x ≫ fP = fP)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (u v : SchemeHomOver t fP),
      pushPt (act x) (act_over x) (LP.mul t u v) =
        LP.mul t (pushPt (act x) (act_over x) u) (pushPt (act x) (act_over x) v))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 P)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (u : SchemeHomOver t fP),
      pushPt (act (x + y)) (act_over (x + y)) u =
        LP.mul t (pushPt (act x) (act_over x) u) (pushPt (act y) (act_over y) u)) :
    ∃ (act' : ↥Λ → (𝒜 ⟶ 𝒜)) (act'_over : ∀ x : ↥Λ, act' x ≫ f = f),
      (∀ x : ↥Λ, act x ≫ g = g ≫ act' x) ∧
      (∀ (x : ↥Λ) (ψ : 𝒜 ⟶ 𝒜), ψ ≫ f = f → act x ≫ g = g ≫ ψ → ψ = act' x) ∧
      (∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t f),
        pushPt (act' x) (act'_over x) (L.mul t u v) =
          L.mul t (pushPt (act' x) (act'_over x) u) (pushPt (act' x) (act'_over x) v)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act' ⟨1, h⟩ = 𝟙 𝒜) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act' ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act' y ≫ act' x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver t f),
        pushPt (act' (x + y)) (act'_over (x + y)) u =
          L.mul t (pushPt (act' x) (act'_over x) u) (pushPt (act' y) (act'_over y) u)) := by

  obtain ⟨v, hv₁, hv₂, hv₃, hv₄, hv₅, hv₆⟩ :=
    main K h𝒜 L (uAct hg act act_over) (fun x S s w₁ w₂ => uAct_hom hg hg_mul act_hom x s w₁ w₂)
  refine ⟨fun x => (v x).1, fun x => (v x).2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x
    have h1 : pullback.fst f (specGenericFibreInclusion R K) ≫ (v x).1 = hg.isoPullback.inv ≫ act x ≫ g := by
      rw [← genericFibreRestrict_coe_comp_fst f f (v x), hv₁ x, uAct_coe, Category.assoc, Category.assoc,
        hg.isoPullback_hom_fst]
    calc act x ≫ g
        = hg.isoPullback.hom ≫ (hg.isoPullback.inv ≫ act x ≫ g) := by simp
      _ = hg.isoPullback.hom ≫ pullback.fst f (specGenericFibreInclusion R K) ≫ (v x).1 := by rw [h1]
      _ = g ≫ (v x).1 := by rw [← Category.assoc, hg.isoPullback_hom_fst]
  ·
    intro x ψ hψ hcomp
    have hres : genericFibreRestrict R K f f ⟨ψ, hψ⟩ = uAct hg act act_over x := by
      apply Subtype.ext
      apply pullback.hom_ext
      · rw [genericFibreRestrict_coe_comp_fst, uAct_coe, Category.assoc, Category.assoc, hg.isoPullback_hom_fst,
          hcomp, ← Category.assoc, hg.isoPullback_inv_fst]
      · rw [genericFibreRestrict_coe_comp_snd]
        exact ((uAct hg act act_over x).2).symm
    exact congrArg Subtype.val (hv₃ x ⟨ψ, hψ⟩ hres)
  ·
    intro x T t u w
    rw [pushPt_eq_schemeHomOverComp, pushPt_eq_schemeHomOverComp, pushPt_eq_schemeHomOverComp]
    exact hv₂ x t u w
  ·
    intro h
    exact congrArg Subtype.val (hv₄ ⟨1, h⟩ (uAct_one hg act_one h))
  ·
    intro x y h
    exact congrArg Subtype.val (hv₅ y x ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ (uAct_mul hg act_mul x y h))
  ·
    intro x y T t u
    rw [pushPt_eq_schemeHomOverComp, pushPt_eq_schemeHomOverComp, pushPt_eq_schemeHomOverComp]
    exact hv₆ x y (x + y) (fun s w => uAct_add hg hg_mul act_add x y s w) t u

end Main

end CerednikDrinfeld.QM.ActionExtension
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle.CerednikDrinfeld.QM.ActionExtension"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle.CerednikDrinfeld"

open CerednikDrinfeld.QM.ActionExtension in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (h𝒜 : AbelianSchemePropertyBundle R f)
    {P : Scheme.{u}} {fP : P ⟶ Spec (CommRingCat.of K)} (LP : RelativeGroupLaw K fP)
    (g : P ⟶ 𝒜) (hg : CategoryTheory.IsPullback g fP f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' fP),
      (LP.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (act : ↥Λ → (P ⟶ P)) (act_over : ∀ x : ↥Λ, act x ≫ fP = fP)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (u v : SchemeHomOver t fP),
      pushPt (act x) (act_over x) (LP.mul t u v) =
        LP.mul t (pushPt (act x) (act_over x) u) (pushPt (act x) (act_over x) v))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 P)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (u : SchemeHomOver t fP),
      pushPt (act (x + y)) (act_over (x + y)) u =
        LP.mul t (pushPt (act x) (act_over x) u) (pushPt (act y) (act_over y) u)) :
    ∃ (act' : ↥Λ → (𝒜 ⟶ 𝒜)) (act'_over : ∀ x : ↥Λ, act' x ≫ f = f),
      (∀ x : ↥Λ, act x ≫ g = g ≫ act' x) ∧
      (∀ (x : ↥Λ) (ψ : 𝒜 ⟶ 𝒜), ψ ≫ f = f → act x ≫ g = g ≫ ψ → ψ = act' x) ∧
      (∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t f),
        pushPt (act' x) (act'_over x) (L.mul t u v) =
          L.mul t (pushPt (act' x) (act'_over x) u) (pushPt (act' x) (act'_over x) v)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act' ⟨1, h⟩ = 𝟙 𝒜) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act' ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act' y ≫ act' x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver t f),
        pushPt (act' (x + y)) (act'_over (x + y)) u =
          L.mul t (pushPt (act' x) (act'_over x) u) (pushPt (act' y) (act'_over y) u)) :=
  fec_main L h𝒜 LP g hg (fun t' x y => hg_mul t' x y) act act_over act_hom act_one act_mul act_add

end S_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle (solution)
