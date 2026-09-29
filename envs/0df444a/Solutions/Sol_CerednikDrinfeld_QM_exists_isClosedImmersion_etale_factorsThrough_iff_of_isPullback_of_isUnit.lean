-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2eb7d6aa-782e-5bd1-a2d5-0457cc9014d1

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_finite_flat_closedSubgroupScheme_of_torsion_genericFibre
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_factor_of_flat_of_genericFibre_iso
import Theorems.Thm_AlgebraicGeometry_existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_pullback_snd_of_isClosedImmersion_of_nsmul_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit
p2m_attr_erase "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit.CerednikDrinfeld.QM"

namespace CerednikDrinfeld
namespace QM
p2m_export "CerednikDrinfeld.QM" "pushPt FactorsThrough nsmulPt FakeEllipticCurve FakeEllipticCurve.IsPullback"
namespace LevelExtension
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

section Powers

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw S f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (n : ℕ) (x : SchemeHomOver t f) : nsmulPt L t n x = L.nsmul t n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show L.mul t (nsmulPt L t n x) x = L.mul t (L.nsmul t n x) x
      rw [ih]

theorem coe_nsmul_eq_comp_schemeNsmul (L : RelativeGroupLaw S f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (x : SchemeHomOver t f) :
    (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x := by
    apply Subtype.ext
    simp
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [hx] at h
  rw [← h]
  rfl

theorem coe_one_eq_comp (L : RelativeGroupLaw S f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
  have h := L.one_natural (𝟙 _) t t (Category.comp_id t)
  rw [← h]
  rfl

theorem pushPt_eq_schemeHomOverComp {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (φ : A ⟶ A) (hφ : φ ≫ f = f) (w : SchemeHomOver t f) :
    pushPt φ hφ w = NeronModelInfra.schemeHomOverComp w ⟨φ, hφ⟩ := rfl

end Powers

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

@[scoped simp] theorem ofP_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of K)} (w : SchemeHomOver t' fP) :
    (ofP hg w).1 = w.1 ≫ hg.isoPullback.hom := rfl

theorem ofP_injective {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) :
    Function.Injective (fun w : SchemeHomOver t' fP => ofP hg w) := by
  intro x y h
  have h' := congrArg Subtype.val h
  simp only [ofP_coe] at h'
  exact Subtype.ext ((cancel_mono hg.isoPullback.hom).1 h')

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

theorem ofP_one (hmul : SquareHom hg L LP) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) :
    ofP hg (LP.one t') = (L.genericFibre K).one t' := by
  set G := L.genericFibre K
  have h : G.mul t' (ofP hg (LP.one t')) (ofP hg (LP.one t')) = ofP hg (LP.one t') := by
    rw [← ofP_mul hg hmul, LP.one_mul]
  calc ofP hg (LP.one t')
      = G.mul t' (G.inv t' (ofP hg (LP.one t'))) (G.mul t' (ofP hg (LP.one t')) (ofP hg (LP.one t'))) := by
          rw [← G.mul_assoc, G.inv_mul_cancel, G.one_mul]
    _ = G.one t' := by rw [h, G.inv_mul_cancel]

theorem ofP_nsmul (hmul : SquareHom hg L LP) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K))
    (n : ℕ) (x : SchemeHomOver t' fP) :
    ofP hg (LP.nsmul t' n x) = (L.genericFibre K).nsmul t' n (ofP hg x) := by
  induction n with
  | zero => exact ofP_one hg hmul t'
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, ofP_mul hg hmul, ih]

end Transport

section SubLaw

variable {S : Type u} [CommRing S] {P C₀ : Scheme.{u}} {fP : P ⟶ Spec (CommRingCat.of S)}
variable (LP : RelativeGroupLaw S fP) (lev₀ : C₀ ⟶ P) [Mono lev₀]

def levPt : SchemeHomOver (lev₀ ≫ fP) fP := ⟨lev₀, rfl⟩

def push {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (z : SchemeHomOver t (lev₀ ≫ fP)) :
    SchemeHomOver t fP :=
  NeronModelInfra.schemeHomOverComp z (levPt lev₀)

omit [Mono lev₀] in
@[scoped simp] theorem push_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (z : SchemeHomOver t (lev₀ ≫ fP)) :
    (push lev₀ z).1 = z.1 ≫ lev₀ := rfl

theorem push_injective {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    Function.Injective (fun z : SchemeHomOver t (lev₀ ≫ fP) => push lev₀ z) := by
  intro x y h
  have h' := congrArg Subtype.val h
  simp only [push_coe] at h'
  exact Subtype.ext ((cancel_mono lev₀).1 h')

omit [Mono lev₀] in
theorem factorsThrough_push {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (z : SchemeHomOver t (lev₀ ≫ fP)) : FactorsThrough lev₀ (push lev₀ z) := ⟨z.1, rfl⟩

omit [Mono lev₀] in
theorem push_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (z : SchemeHomOver t (lev₀ ≫ fP)) :
    push lev₀ (GoodReductionJacobian.schemeHomOverComp ψ hψ z) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (push lev₀ z) := by
  apply Subtype.ext
  simp

noncomputable def pull {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t fP)
    (hx : FactorsThrough lev₀ x) : SchemeHomOver t (lev₀ ≫ fP) :=
  ⟨hx.choose, by rw [← Category.assoc, hx.choose_spec]; exact x.2⟩

omit [Mono lev₀] in
@[scoped simp] theorem push_pull {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t fP)
    (hx : FactorsThrough lev₀ x) : push lev₀ (pull lev₀ x hx) = x :=
  Subtype.ext hx.choose_spec

variable (hsub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t fP),
    FactorsThrough lev₀ x → FactorsThrough lev₀ y →
      FactorsThrough lev₀ (LP.mul t x y) ∧ FactorsThrough lev₀ (LP.inv t x))
variable (hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), FactorsThrough lev₀ (LP.one t))

noncomputable def subLaw : RelativeGroupLaw S (lev₀ ≫ fP) where
  mul t z w := pull lev₀ (LP.mul t (push lev₀ z) (push lev₀ w))
    (hsub t _ _ (factorsThrough_push lev₀ z) (factorsThrough_push lev₀ w)).1
  one t := pull lev₀ (LP.one t) (hone t)
  inv t z := pull lev₀ (LP.inv t (push lev₀ z))
    (hsub t _ _ (factorsThrough_push lev₀ z) (factorsThrough_push lev₀ z)).2
  mul_assoc t x y z := by
    apply push_injective lev₀
    simp only [push_pull, LP.mul_assoc]
  one_mul t x := by
    apply push_injective lev₀
    simp only [push_pull, LP.one_mul]
  mul_one t x := by
    apply push_injective lev₀
    simp only [push_pull, LP.mul_one]
  inv_mul_cancel t x := by
    apply push_injective lev₀
    simp only [push_pull, LP.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply push_injective lev₀
    simp only [push_natural, push_pull, LP.mul_natural]

theorem push_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (z w : SchemeHomOver t (lev₀ ≫ fP)) :
    push lev₀ ((subLaw LP lev₀ hsub hone).mul t z w) = LP.mul t (push lev₀ z) (push lev₀ w) :=
  push_pull lev₀ _ _

end SubLaw

section Reduced

variable {K : Type u} [Field K]

theorem isReduced_of_isClosedImmersion_of_isFinite {X Y : Scheme.{u}} (j : X ⟶ Y) [IsClosedImmersion j]
    (q : Y ⟶ Spec (CommRingCat.of K)) [IsFinite q] [IsReduced Y] : IsReduced X := by
  haveI : IsAffine Y := isAffine_of_isAffineHom q
  haveI : IsAffine X := isAffine_of_isAffineHom j

  have hfin : q.appTop.hom.Finite := q.finite_appTop
  let φ : K →+* Γ(Y, ⊤) := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hφ : φ.Finite :=
    RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  letI : Algebra K Γ(Y, ⊤) := φ.toAlgebra
  haveI : Module.Finite K Γ(Y, ⊤) := hφ
  haveI : IsArtinianRing Γ(Y, ⊤) := IsArtinianRing.of_finite K Γ(Y, ⊤)
  haveI : IsSemisimpleRing Γ(Y, ⊤) := IsArtinianRing.isSemisimpleRing_of_isReduced Γ(Y, ⊤)

  have hsurj : Function.Surjective j.appTop := (IsClosedImmersion.isAffine_surjective_of_isAffine j).2
  haveI : IsSemisimpleRing Γ(X, ⊤) := RingHom.isSemisimpleRing_of_surjective j.appTop.hom hsurj
  haveI : _root_.IsReduced Γ(X, ⊤) := inferInstance
  exact isReduced_of_isAffine_isReduced X

end Reduced

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
variable {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)}
variable {P : Scheme.{u}} {fP : P ⟶ Spec (CommRingCat.of K)}

theorem main (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (h𝒜 : AbelianSchemePropertyBundle R f)
    (LP : RelativeGroupLaw K fP) (hcP : LP.IsCommutative) (hP : AbelianSchemePropertyBundle K fP)
    (g : P ⟶ 𝒜) (hg : IsPullback g fP f (specGenericFibreInclusion R K))
    (hg_mul : SquareHom hg L LP)
    {ι : Type v} (act : ι → (P ⟶ P)) (act_over : ∀ i, act i ≫ fP = fP)
    (act' : ι → (𝒜 ⟶ 𝒜)) (act'_over : ∀ i, act' i ≫ f = f)
    (hact : ∀ i, act i ≫ g = g ≫ act' i)
    (N : ℕ) (hN : IsUnit ((N : ℕ) : R))
    {C₀ : Scheme.{u}} (lev₀ : C₀ ⟶ P) (lev₀_closed : IsClosedImmersion lev₀)
    (lev₀_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t fP),
      FactorsThrough lev₀ x → FactorsThrough lev₀ y →
        FactorsThrough lev₀ (LP.mul t x y) ∧ FactorsThrough lev₀ (LP.inv t x))
    (lev₀_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)), FactorsThrough lev₀ (LP.one t))
    (lev₀_torsion : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t fP),
      FactorsThrough lev₀ x → nsmulPt LP t N x = LP.one t)
    (lev₀_stable : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t fP),
      FactorsThrough lev₀ x → FactorsThrough lev₀ (pushPt (act i) (act_over i) x))
    (lev₀_finite : IsFinite (lev₀ ≫ fP)) (lev₀_flat : Flat (lev₀ ≫ fP))
    (lev₀_rank : ∀ s : ↥(Spec (CommRingCat.of K)), (lev₀ ≫ fP).finrank s = N ^ 2) :
    ∃ (C : Scheme.{u}) (lev : C ⟶ 𝒜), IsClosedImmersion lev ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        FactorsThrough lev x → FactorsThrough lev y →
          FactorsThrough lev (L.mul t x y) ∧ FactorsThrough lev (L.inv t x)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough lev (L.one t)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        FactorsThrough lev x → nsmulPt L t N x = L.one t) ∧
      (∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        FactorsThrough lev x → FactorsThrough lev (pushPt (act' i) (act'_over i) x)) ∧
      IsFinite (lev ≫ f) ∧ Flat (lev ≫ f) ∧ LocallyOfFinitePresentation (lev ≫ f) ∧ Etale (lev ≫ f) ∧
      (∀ s : ↥(Spec (CommRingCat.of R)), (lev ≫ f).finrank s = N ^ 2) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t' fP),
        FactorsThrough lev₀ x ↔ ∃ x₀ : T ⟶ C, x₀ ≫ lev = x.1 ≫ g) := by
  classical
  haveI := lev₀_closed
  haveI := lev₀_finite
  haveI := lev₀_flat
  set ιK := specGenericFibreInclusion R K with hιK

  have hNK : IsUnit ((N : ℕ) : K) := by simpa using hN.map (algebraMap R K)

  haveI : IsSeparated f := by haveI := h𝒜.proper; infer_instance
  haveI : IsSeparated fP := by haveI := hP.proper; infer_instance
  obtain ⟨hNfin, hNflat⟩ :=
    RelativeGroupLaw.isFinite_and_flat_schemeNsmul_of_isUnit L h𝒜 (fun t x y => hc t x y) N hN
  haveI := hNfin
  haveI : IsFinite (L.schemeKerStr N) := MorphismProperty.pullback_snd _ _ hNfin
  obtain ⟨hNfinP, hNflatP⟩ :=
    RelativeGroupLaw.isFinite_and_flat_schemeNsmul_of_isUnit LP hP (fun t x y => hcP t x y) N hNK
  haveI := hNfinP
  haveI := hNflatP
  haveI : IsFinite (LP.schemeKerStr N) := MorphismProperty.pullback_snd _ _ hNfinP

  haveI : LocallyOfFiniteType fP := by haveI := hP.smooth; infer_instance
  haveI : IsReduced (LP.schemeKer N) :=
    RelativeGroupLaw.isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit (R := K) (K := K)
      (by intro a b h; simpa using h) LP (fun t x y => hcP t x y) N hNK

  have htaut : FactorsThrough lev₀ (levPt lev₀ (fP := fP)) := ⟨𝟙 C₀, Category.id_comp _⟩
  have htorsK : LP.nsmul (lev₀ ≫ fP) N (levPt lev₀) = LP.one (lev₀ ≫ fP) := by
    rw [← nsmulPt_eq_nsmul]; exact lev₀_torsion _ _ htaut

  have hcomm_sq : lev₀ ≫ LP.schemeNsmul N = (lev₀ ≫ fP) ≫ (LP.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
    have h1 := coe_nsmul_eq_comp_schemeNsmul LP (lev₀ ≫ fP) N (levPt lev₀)
    rw [htorsK, coe_one_eq_comp] at h1
    exact h1.symm
  let jK : C₀ ⟶ LP.schemeKer N := pullback.lift lev₀ (lev₀ ≫ fP) hcomm_sq
  have hjK : jK ≫ pullback.fst _ _ = lev₀ := pullback.lift_fst _ _ _
  haveI : IsClosedImmersion (jK ≫ pullback.fst (LP.schemeNsmul N) (LP.one (𝟙 _)).1) := by
    rw [hjK]; infer_instance
  haveI hsecK : IsClosedImmersion (LP.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
    have h2 : IsClosedImmersion ((LP.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ fP) := by
      rw [(LP.one (𝟙 _)).2]; infer_instance
    exact IsClosedImmersion.of_comp _ fP
  haveI : IsClosedImmersion (pullback.fst (LP.schemeNsmul N) (LP.one (𝟙 _)).1) :=
    MorphismProperty.pullback_fst _ _ hsecK
  haveI : IsClosedImmersion jK := IsClosedImmersion.of_comp jK (pullback.fst (LP.schemeNsmul N) (LP.one (𝟙 _)).1)
  haveI : IsReduced C₀ := isReduced_of_isClosedImmersion_of_isFinite jK (LP.schemeKerStr N)

  let LC₀ := subLaw LP lev₀ lev₀_sub lev₀_one
  let iK : SchemeHomOver (lev₀ ≫ fP) (pullback.snd f ιK) :=
    ⟨lev₀ ≫ hg.isoPullback.hom, by rw [Category.assoc, hg.isoPullback_hom_snd]⟩
  have hiK_coe : iK.1 = lev₀ ≫ hg.isoPullback.hom := rfl
  have hci : IsClosedImmersion iK.1 := by rw [hiK_coe]; infer_instance
  have hcomp_iK : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t (lev₀ ≫ fP)),
      NeronModelInfra.schemeHomOverComp z iK = ofP hg (push lev₀ z) := by
    intro T t z
    apply Subtype.ext
    simp only [NeronModelInfra.schemeHomOverComp_coe, hiK_coe, ofP_coe, push_coe, Category.assoc]
  have hiK : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t (lev₀ ≫ fP)),
      NeronModelInfra.schemeHomOverComp (LC₀.mul t x y) iK =
        (L.genericFibre K).mul t (NeronModelInfra.schemeHomOverComp x iK)
          (NeronModelInfra.schemeHomOverComp y iK) := by
    intro T t x y
    rw [hcomp_iK, hcomp_iK, hcomp_iK, push_mul, ofP_mul hg hg_mul]
  have hNK' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t (lev₀ ≫ fP)),
      (L.genericFibre K).nsmul t N (NeronModelInfra.schemeHomOverComp x iK) = (L.genericFibre K).one t := by
    intro T t x
    rw [hcomp_iK, ← ofP_nsmul hg hg_mul, ← nsmulPt_eq_nsmul, lev₀_torsion t _ (factorsThrough_push lev₀ x),
      ofP_one hg hg_mul]

  obtain ⟨E, lev, hclosed, hfin, hflat, hfp, h_one, h_mul, h_inv, e, he_iso, he_comp⟩ :=
    RelativeGroupLaw.exists_finite_flat_closedSubgroupScheme_of_torsion_genericFibre K L N LC₀ iK hci hiK hNK'
  haveI := hclosed
  haveI := hfin
  haveI := hflat
  haveI := hfp
  haveI := he_iso

  have he2 : e.1 ≫ (lev₀ ≫ fP) = pullback.snd (lev ≫ f) ιK := e.2
  have hmapfst : pullback.map (lev ≫ f) ιK f ιK lev (𝟙 _) (𝟙 _) (Category.comp_id _)
        (by rw [Category.comp_id, Category.id_comp]) ≫ pullback.fst f ιK = pullback.fst (lev ≫ f) ιK ≫ lev := by
    rw [pullback.lift_fst]

  have hkey : inv e.1 ≫ pullback.fst (lev ≫ f) ιK ≫ lev = lev₀ ≫ g := by
    have h1 : pullback.fst (lev ≫ f) ιK ≫ lev = e.1 ≫ iK.1 ≫ pullback.fst f ιK := by
      rw [← hmapfst, ← Category.assoc, ← he_comp]
    rw [h1, IsIso.inv_hom_id_assoc, hiK_coe, Category.assoc, hg.isoPullback_hom_fst]
  have hkey' : pullback.fst (lev ≫ f) ιK ≫ lev = e.1 ≫ lev₀ ≫ g := by
    rw [← hkey, IsIso.hom_inv_id_assoc]

  have htors : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      FactorsThrough lev x → L.nsmul t N x = L.one t := by
    intro T t x hx
    exact RelativeGroupLaw.nsmul_eq_one_of_factor_of_flat_of_genericFibre_iso K L N iK hNK' lev e he_iso he_comp
      t x hx
  refine ⟨E, lev, hclosed, fun t x y hx hy => ⟨h_mul t x y hx hy, h_inv t x hx⟩, fun t => h_one t, ?_, ?_,
    hfin, hflat, hfp, ?_, ?_, ?_⟩
  ·
    intro T t x hx
    rw [nsmulPt_eq_nsmul]
    exact htors t x hx
  ·
    intro i T t x hx
    obtain ⟨s₀, hs₀⟩ := lev₀_stable i (lev₀ ≫ fP) (levPt lev₀) htaut
    have hs₀' : s₀ ≫ lev₀ = lev₀ ≫ act i := hs₀
    let ψK : pullback (lev ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ E :=
      e.1 ≫ s₀ ≫ inv e.1 ≫ pullback.fst (lev ≫ f) ιK
    have hψK : ψK ≫ lev = pullback.fst (lev ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ lev ≫ act' i := by
      show (e.1 ≫ s₀ ≫ inv e.1 ≫ pullback.fst (lev ≫ f) ιK) ≫ lev = pullback.fst (lev ≫ f) ιK ≫ lev ≫ act' i
      simp only [Category.assoc]
      rw [hkey, reassoc_of% hs₀', hact i, ← Category.assoc (pullback.fst _ _), hkey']
      simp only [Category.assoc]
    obtain ⟨φ, hφ, -⟩ :=
      AlgebraicGeometry.existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq K (lev ≫ f) lev
        (lev ≫ act' i) ψK hψK
    obtain ⟨x₀, hx₀⟩ := hx
    refine ⟨x₀ ≫ φ, ?_⟩
    rw [Category.assoc, hφ, ← Category.assoc, hx₀]
    rfl
  ·
    have htorsE : L.nsmul (lev ≫ f) N ⟨lev, rfl⟩ = L.one (lev ≫ f) :=
      htors (lev ≫ f) ⟨lev, rfl⟩ ⟨𝟙 E, Category.id_comp _⟩
    have hfu : FormallyUnramified (pullback.snd (lev ≫ f) (𝟙 (Spec (CommRingCat.of R)))) :=
      RelativeGroupLaw.formallyUnramified_pullback_snd_of_isClosedImmersion_of_nsmul_eq_one (𝟙 _) L
        (fun t x y => hc t x y) N hN lev htorsE
    have heq : lev ≫ f = inv (pullback.fst (lev ≫ f) (𝟙 (Spec (CommRingCat.of R)))) ≫
        pullback.snd (lev ≫ f) (𝟙 (Spec (CommRingCat.of R))) := by
      rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
    haveI : FormallyUnramified (lev ≫ f) := by
      rw [heq]
      exact (MorphismProperty.cancel_left_of_respectsIso @FormallyUnramified _ _).mpr hfu
    exact Etale.of_formallyUnramified_of_flat (lev ≫ f)
  ·
    have hlc := Scheme.Hom.isLocallyConstant_finrank (lev ≫ f)
    haveI : PreconnectedSpace ↥(Spec (CommRingCat.of R)) :=
      inferInstanceAs (PreconnectedSpace (PrimeSpectrum R))
    let pt : ↥(Spec (CommRingCat.of K)) := ⟨⊥, Ideal.isPrime_bot⟩
    have hgen : (lev ≫ f).finrank (ιK.base pt) = N ^ 2 := by
      rw [← Scheme.Hom.finrank_pullback_snd (lev ≫ f) ιK pt, ← he2, Scheme.Hom.finrank_comp_left_of_isIso]
      exact lev₀_rank pt
    intro s
    rw [hlc.apply_eq_of_preconnectedSpace s (ιK.base pt)]
    exact hgen
  ·
    intro T t' x
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z ≫ inv e.1 ≫ pullback.fst (lev ≫ f) ιK, ?_⟩
      simp only [Category.assoc]
      rw [hkey, ← Category.assoc, hz]
    · rintro ⟨x₀, hx₀⟩
      have hw : x₀ ≫ (lev ≫ f) = t' ≫ ιK := by
        rw [← Category.assoc, hx₀, Category.assoc, hg.w, ← Category.assoc, x.2]
      let y : T ⟶ pullback (lev ≫ f) ιK := pullback.lift x₀ t' hw
      refine ⟨y ≫ e.1, ?_⟩
      apply (cancel_mono hg.isoPullback.hom).1
      apply pullback.hom_ext
      · simp only [Category.assoc, hg.isoPullback_hom_fst]
        rw [← hkey', pullback.lift_fst_assoc, hx₀]
      · simp only [Category.assoc, hg.isoPullback_hom_snd]
        rw [x.2, he2, pullback.lift_snd]

end Main

end CerednikDrinfeld.QM.LevelExtension
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit.CerednikDrinfeld.QM.LevelExtension"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit.CerednikDrinfeld"

open CerednikDrinfeld.QM.LevelExtension in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (h𝒜 : AbelianSchemePropertyBundle R f)
    {P : Scheme.{u}} {fP : P ⟶ Spec (CommRingCat.of K)} (LP : RelativeGroupLaw K fP) (hcP : LP.IsCommutative)
    (hP : AbelianSchemePropertyBundle K fP)
    (g : P ⟶ 𝒜) (hg : CategoryTheory.IsPullback g fP f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' fP),
      (LP.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    {ι : Type v} (act : ι → (P ⟶ P)) (act_over : ∀ i : ι, act i ≫ fP = fP)
    (act' : ι → (𝒜 ⟶ 𝒜)) (act'_over : ∀ i : ι, act' i ≫ f = f)
    (hact : ∀ i : ι, act i ≫ g = g ≫ act' i)
    (N : ℕ) (hN : IsUnit ((N : ℕ) : R))
    {C₀ : Scheme.{u}} (lev₀ : C₀ ⟶ P) (lev₀_closed : IsClosedImmersion lev₀)
    (lev₀_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t fP),
      FactorsThrough lev₀ x → FactorsThrough lev₀ y →
        FactorsThrough lev₀ (LP.mul t x y) ∧ FactorsThrough lev₀ (LP.inv t x))
    (lev₀_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)), FactorsThrough lev₀ (LP.one t))
    (lev₀_torsion : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t fP),
      FactorsThrough lev₀ x → nsmulPt LP t N x = LP.one t)
    (lev₀_stable : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t fP),
      FactorsThrough lev₀ x → FactorsThrough lev₀ (pushPt (act i) (act_over i) x))
    (lev₀_finite : IsFinite (lev₀ ≫ fP)) (lev₀_flat : Flat (lev₀ ≫ fP))
    (lev₀_rank : ∀ s : ↥(Spec (CommRingCat.of K)), (lev₀ ≫ fP).finrank s = N ^ 2) :
    ∃ (C : Scheme.{u}) (lev : C ⟶ 𝒜), IsClosedImmersion lev ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        FactorsThrough lev x → FactorsThrough lev y →
          FactorsThrough lev (L.mul t x y) ∧ FactorsThrough lev (L.inv t x)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough lev (L.one t)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        FactorsThrough lev x → nsmulPt L t N x = L.one t) ∧
      (∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        FactorsThrough lev x → FactorsThrough lev (pushPt (act' i) (act'_over i) x)) ∧
      IsFinite (lev ≫ f) ∧ Flat (lev ≫ f) ∧ LocallyOfFinitePresentation (lev ≫ f) ∧ Etale (lev ≫ f) ∧
      (∀ s : ↥(Spec (CommRingCat.of R)), (lev ≫ f).finrank s = N ^ 2) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t' fP),
        FactorsThrough lev₀ x ↔ ∃ x₀ : T ⟶ C, x₀ ≫ lev = x.1 ≫ g) :=
  main L hc h𝒜 LP hcP hP g hg (fun t' x y => hg_mul t' x y) act act_over act' act'_over hact N hN lev₀
    lev₀_closed lev₀_sub lev₀_one lev₀_torsion lev₀_stable lev₀_finite lev₀_flat lev₀_rank

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit.CerednikDrinfeld.QM.LevelExtension"

end S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit (solution)
