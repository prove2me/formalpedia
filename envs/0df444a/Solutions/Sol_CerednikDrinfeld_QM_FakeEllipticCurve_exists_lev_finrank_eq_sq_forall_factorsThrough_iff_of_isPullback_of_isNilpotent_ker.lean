-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_lev_finrank_eq_sq_forall_factorsThrough_iff_of_isPullback_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d587efad-009f-5f73-82d2-f77e5cdfe7eb

import Mathlib
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Theorems.Thm_AlgebraicGeometry_isFinite_and_etale_comp_of_isOpenImmersion_of_isClosed_range
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_lev_finrank_eq_sq_forall_factorsThrough_iff_of_isPullback_of_isNilpotent_ker
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM"
open scoped Quaternion

noncomputable section

namespace LevLiftExistsBody

section Kernel

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem nsmul_eq_nsmulPt {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    L.nsmul t n P = nsmulPt L t n P := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show L.mul t (L.nsmul t n P) P = L.mul t (nsmulPt L t n P) P
    rw [ih]

theorem coe_nsmulPt {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    (nsmulPt L t n P).1 = P.1 ≫ L.schemeNsmul n := by
  have hnat := L.nsmul_natural f t P.1 P.2 n RelativeGroupLaw.idPoint
  have hid : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P :=
    Subtype.ext (Category.comp_id _)
  rw [hid, nsmul_eq_nsmulPt, nsmul_eq_nsmulPt] at hnat
  rw [← hnat]
  show P.1 ≫ (nsmulPt L f n RelativeGroupLaw.idPoint).1 = P.1 ≫ (L.nsmul f n RelativeGroupLaw.idPoint).1
  rw [nsmul_eq_nsmulPt]

theorem coe_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
  have h := L.one_natural (𝟙 _) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

abbrev kerι (n : ℕ) : L.schemeKer n ⟶ A :=
  pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of S)))).1

theorem kerι_f (n : ℕ) : kerι L n ≫ f = L.schemeKerStr n := by
  have h1 : kerι L n ≫ f = kerι L n ≫ (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over n]
  rw [h1, ← Category.assoc, pullback.condition, Category.assoc,
    (L.one (𝟙 (Spec (CommRingCat.of S)))).2, Category.comp_id]

def kerLift {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (n : ℕ) (P : SchemeHomOver t f)
    (hP : nsmulPt L t n P = L.one t) : T ⟶ L.schemeKer n :=
  pullback.lift P.1 t (by rw [← coe_nsmulPt, hP, coe_one])

@[scoped simp, reassoc] theorem kerLift_kerι {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (n : ℕ) (P : SchemeHomOver t f)
    (hP : nsmulPt L t n P = L.one t) : kerLift L n P hP ≫ kerι L n = P.1 :=
  pullback.lift_fst _ _ _

@[scoped simp, reassoc] theorem kerLift_str {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (n : ℕ) (P : SchemeHomOver t f)
    (hP : nsmulPt L t n P = L.one t) : kerLift L n P hP ≫ L.schemeKerStr n = t :=
  pullback.lift_snd _ _ _

theorem nsmulPt_eq_one_of_comp_kerι (n : ℕ) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t f) (Q : T ⟶ L.schemeKer n) (hQ : Q ≫ kerι L n = P.1) :
    nsmulPt L t n P = L.one t := by
  apply Subtype.ext
  have ht : t = Q ≫ L.schemeKerStr n := by rw [← kerι_f, ← Category.assoc, hQ, P.2]
  rw [coe_nsmulPt, coe_one, ← hQ, Category.assoc, pullback.condition, ht, Category.assoc]

theorem isClosedImmersion_one [IsSeparated f] :
    IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
  haveI : IsClosedImmersion ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f) := by
    rw [(L.one (𝟙 (Spec (CommRingCat.of S)))).2]; infer_instance
  exact IsClosedImmersion.of_comp _ f

theorem isClosedImmersion_kerι [IsSeparated f] (n : ℕ) : IsClosedImmersion (kerι L n) := by
  haveI := isClosedImmersion_one L
  infer_instance

end Kernel

section PointGroups

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem nsmulPt_eq_pow {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n P = @HPow.hPow _ ℕ _ (@instHPow _ ℕ (L.pointGroup t).toMonoid.toPow) P n := by
  letI := L.pointGroup t
  induction n with
  | zero => exact (pow_zero P).symm
  | succ n ih =>
    show L.mul t (nsmulPt L t n P) P = P ^ (n + 1)
    rw [ih, pow_succ]; rfl

theorem nsmulPt_mul_inv_eq_one (hcomm : L.IsCommutative) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ)
    (P Q : SchemeHomOver t f) (hP : nsmulPt L t n P = L.one t) (hQ : nsmulPt L t n Q = L.one t) :
    nsmulPt L t n (L.mul t P Q) = L.one t ∧ nsmulPt L t n (L.inv t P) = L.one t := by
  letI := L.pointGroup t
  rw [nsmulPt_eq_pow] at hP hQ ⊢
  rw [nsmulPt_eq_pow]
  constructor
  · show (P * Q) ^ n = 1
    have hc : Commute P Q := hcomm t P Q
    rw [hc.mul_pow]
    change P ^ n = 1 at hP
    change Q ^ n = 1 at hQ
    rw [hP, hQ, one_mul]
  · show P⁻¹ ^ n = 1
    change P ^ n = 1 at hP
    rw [inv_pow, hP, inv_one]

theorem nsmulPt_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) :
    nsmulPt L t n (L.one t) = L.one t := by
  letI := L.pointGroup t
  rw [nsmulPt_eq_pow]
  exact one_pow n

theorem inv_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t
  letI := L.pointGroup t'
  have h : schemeHomOverComp ψ hψ (L.inv t x) * schemeHomOverComp ψ hψ x = 1 := by
    show L.mul t' _ _ = L.one t'
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, L.one_natural t t' ψ hψ]
  exact eq_inv_of_mul_eq_one_left h

theorem nsmulPt_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n x) = nsmulPt L t' n (schemeHomOverComp ψ hψ x) := by
  rw [← nsmul_eq_nsmulPt, ← nsmul_eq_nsmulPt]
  exact L.nsmul_natural t t' ψ hψ n x

theorem coe_mul_cast {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t') (P Q : SchemeHomOver t f) :
    (L.mul t' ⟨P.1, P.2.trans h⟩ ⟨Q.1, Q.2.trans h⟩).1 = (L.mul t P Q).1 := by
  subst h; rfl

end PointGroups

section HomMaps

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
variable {S' : Type} [CommRing S'] {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of S')} (L' : RelativeGroupLaw S' f')

theorem map_one_inv_nsmulPt {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) {T' : Scheme.{0}}
    (t' : T' ⟶ Spec (CommRingCat.of S')) (φ : SchemeHomOver t f → SchemeHomOver t' f')
    (hφ : ∀ x y, φ (L.mul t x y) = L'.mul t' (φ x) (φ y)) :
    φ (L.one t) = L'.one t' ∧ (∀ x, φ (L.inv t x) = L'.inv t' (φ x)) ∧
      ∀ (n : ℕ) x, φ (nsmulPt L t n x) = nsmulPt L' t' n (φ x) := by
  letI := L.pointGroup t
  letI := L'.pointGroup t'
  let Φ : SchemeHomOver t f →* SchemeHomOver t' f' := MonoidHom.mk' φ hφ
  refine ⟨map_one Φ, fun x => map_inv Φ x, fun n x => ?_⟩
  rw [nsmulPt_eq_pow, nsmulPt_eq_pow]
  exact map_pow Φ x n

end HomMaps

section Base

variable {S S₀ : Type} [CommRing S] [CommRing S₀] (p : S →+* S₀) (hp : Function.Surjective p)
  (hI : IsNilpotent (RingHom.ker p))

include hI in
theorem ker_le_of_isPrime (𝔮 : Ideal S) [𝔮.IsPrime] : RingHom.ker p ≤ 𝔮 := by
  obtain ⟨n, hn⟩ := hI
  intro x hx
  have hxn : x ^ n ∈ RingHom.ker p ^ n := Ideal.pow_mem_pow hx n
  rw [hn] at hxn
  have hx0 : x ^ n = 0 := hxn
  exact Ideal.IsPrime.mem_of_pow_mem ‹_› n (hx0 ▸ 𝔮.zero_mem)

include hp in
theorem isClosedImmersion_specMap : IsClosedImmersion (Spec.map (CommRingCat.ofHom p)) :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom p) (fun y => by
    obtain ⟨x, hx⟩ := hp y; exact ⟨x, hx⟩)

include hp hI in
theorem surjective_specMap : Surjective (Spec.map (CommRingCat.ofHom p)) := by
  refine ⟨fun 𝔮 => ?_⟩
  haveI : 𝔮.asIdeal.IsPrime := 𝔮.isPrime
  have hle : RingHom.ker p ≤ 𝔮.asIdeal := ker_le_of_isPrime p hI 𝔮.asIdeal
  haveI : (𝔮.asIdeal.map p).IsPrime := Ideal.map_isPrime_of_surjective hp hle
  refine ⟨⟨𝔮.asIdeal.map p, inferInstance⟩, ?_⟩
  apply PrimeSpectrum.ext
  rw [Spec.map_apply]
  show Ideal.comap (CommRingCat.ofHom p).hom (Ideal.map p 𝔮.asIdeal) = 𝔮.asIdeal
  rw [CommRingCat.hom_ofHom, Ideal.comap_map_of_surjective p hp, sup_eq_left]
  intro x hx
  exact hle hx

include hI in

theorem ker_le_ker {K : Type} [CommRing K] [IsReduced K] (φ : S →+* K) : RingHom.ker p ≤ RingHom.ker φ := by
  obtain ⟨n, hn⟩ := hI
  intro x hx
  have hxn : x ^ n ∈ RingHom.ker p ^ n := Ideal.pow_mem_pow hx n
  rw [hn] at hxn
  have hx0 : x ^ n = 0 := hxn
  have : IsNilpotent (φ x) := ⟨n, by rw [← map_pow, hx0, map_zero]⟩
  exact this.eq_zero

include hp hI in

theorem exists_eq_comp {K : Type} [CommRing K] [IsReduced K] (φ : S →+* K) : ∃ φ₀ : S₀ →+* K, φ = φ₀.comp p :=
  ⟨RingHom.liftOfSurjective p hp ⟨φ, ker_le_ker p hI φ⟩, (RingHom.liftOfSurjective_comp p hp ⟨φ, ker_le_ker p hI φ⟩).symm⟩

include hp hI in

theorem exists_eq_comp_specMap {K : Type} [Field K] (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S)) :
    ∃ b₀ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S₀), b = b₀ ≫ Spec.map (CommRingCat.ofHom p) := by
  obtain ⟨φ₀, hφ₀⟩ := exists_eq_comp p hp hI (Spec.preimage b).hom
  refine ⟨Spec.map (CommRingCat.ofHom φ₀), ?_⟩
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hφ₀, CommRingCat.ofHom_hom, Spec.map_preimage]

end Base

section Main

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

structure Setup (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) (S S₀ : Type) [CommRing S] [CommRing S₀] where
  p : S →+* S₀
  hp : Function.Surjective p
  hI : IsNilpotent (RingHom.ker p)
  E₀ : FakeEllipticCurve Λ N S₀
  A : Scheme.{0}
  f : A ⟶ Spec (CommRingCat.of S)
  sep : IsSeparated f
  L : RelativeGroupLaw S f
  hN : IsUnit ((N : ℕ) : S)
  hfin : IsFinite (L.schemeKerStr N)
  het : Etale (L.schemeKerStr N)
  g : E₀.A ⟶ A
  hg : CategoryTheory.IsPullback g E₀.f f (Spec.map (CommRingCat.ofHom p))
  hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom p))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1

variable {S S₀ : Type} [CommRing S] [CommRing S₀] (X : Setup Λ N S S₀)

scoped instance : IsSeparated X.f := X.sep

def gPt {T : Scheme.{0}} {t₀ : T ⟶ Spec (CommRingCat.of S₀)} (P : SchemeHomOver t₀ X.E₀.f) :
    SchemeHomOver (t₀ ≫ Spec.map (CommRingCat.ofHom X.p)) X.f :=
  ⟨P.1 ≫ X.g, by rw [Category.assoc, X.hg.w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem gPt_coe {T : Scheme.{0}} {t₀ : T ⟶ Spec (CommRingCat.of S₀)} (P : SchemeHomOver t₀ X.E₀.f) :
    (gPt X P).1 = P.1 ≫ X.g := rfl

def liftPt {T : Scheme.{0}} {t₀ : T ⟶ Spec (CommRingCat.of S₀)}
    (P : SchemeHomOver (t₀ ≫ Spec.map (CommRingCat.ofHom X.p)) X.f) : SchemeHomOver t₀ X.E₀.f :=
  ⟨X.hg.lift P.1 t₀ P.2, X.hg.lift_snd _ _ _⟩

@[scoped simp] theorem gPt_liftPt {T : Scheme.{0}} {t₀ : T ⟶ Spec (CommRingCat.of S₀)}
    (P : SchemeHomOver (t₀ ≫ Spec.map (CommRingCat.ofHom X.p)) X.f) : gPt X (liftPt X P) = P :=
  Subtype.ext (X.hg.lift_fst _ _ _)

theorem gPt_injective {T : Scheme.{0}} (t₀ : T ⟶ Spec (CommRingCat.of S₀)) :
    Function.Injective (gPt X (T := T) (t₀ := t₀)) := by
  haveI : IsClosedImmersion X.g :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback X.hg.flip (isClosedImmersion_specMap X.p X.hp)
  intro P Q h
  have h1 := congrArg Subtype.val h
  simp only [gPt_coe] at h1
  exact Subtype.ext (Mono.right_cancellation _ _ h1)

theorem liftPt_gPt {T : Scheme.{0}} {t₀ : T ⟶ Spec (CommRingCat.of S₀)} (P : SchemeHomOver t₀ X.E₀.f)
    (hinj : Function.Injective (gPt X (T := T) (t₀ := t₀))) : liftPt X (gPt X P) = P :=
  hinj (gPt_liftPt X _)

theorem gPt_mul {T : Scheme.{0}} (t₀ : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t₀ X.E₀.f) :
    gPt X (X.E₀.L.mul t₀ P Q) = X.L.mul _ (gPt X P) (gPt X Q) :=
  Subtype.ext (X.hmul t₀ P Q)

theorem gPt_one_inv_nsmulPt {T : Scheme.{0}} (t₀ : T ⟶ Spec (CommRingCat.of S₀)) :
    gPt X (X.E₀.L.one t₀) = X.L.one _ ∧ (∀ x, gPt X (X.E₀.L.inv t₀ x) = X.L.inv _ (gPt X x)) ∧
      ∀ (n : ℕ) x, gPt X (nsmulPt X.E₀.L t₀ n x) = nsmulPt X.L _ n (gPt X x) :=
  map_one_inv_nsmulPt X.E₀.L X.L t₀ _ (gPt X) (gPt_mul X t₀)

theorem liftPt_mul {T : Scheme.{0}} (t₀ : T ⟶ Spec (CommRingCat.of S₀))
    (P Q : SchemeHomOver (t₀ ≫ Spec.map (CommRingCat.ofHom X.p)) X.f) :
    liftPt X (X.L.mul _ P Q) = X.E₀.L.mul t₀ (liftPt X P) (liftPt X Q) := by
  apply gPt_injective X t₀
  rw [gPt_mul X, gPt_liftPt, gPt_liftPt, gPt_liftPt]

theorem nsmulPt_gPt_eq_one_iff {T : Scheme.{0}} (t₀ : T ⟶ Spec (CommRingCat.of S₀)) (n : ℕ) (P : SchemeHomOver t₀ X.E₀.f) :
    nsmulPt X.L _ n (gPt X P) = X.L.one _ ↔ nsmulPt X.E₀.L t₀ n P = X.E₀.L.one t₀ := by
  obtain ⟨h1, -, hn⟩ := gPt_one_inv_nsmulPt X t₀
  rw [← hn, ← h1]
  exact ⟨fun h => gPt_injective X t₀ h, fun h => by rw [h]⟩

include X in
theorem isUnit_S₀ : IsUnit ((N : ℕ) : S₀) := by
  have := X.hN.map X.p
  rwa [map_natCast] at this

def j₀ : X.E₀.C ⟶ X.E₀.L.schemeKer N :=
  kerLift X.E₀.L N (⟨X.E₀.lev, rfl⟩ : SchemeHomOver (X.E₀.lev ≫ X.E₀.f) X.E₀.f) (X.E₀.lev_torsion _ _ ⟨𝟙 _, Category.id_comp _⟩)

@[scoped simp, reassoc] theorem j₀_kerι : j₀ X ≫ kerι X.E₀.L N = X.E₀.lev := kerLift_kerι _ _ _ _

@[scoped simp, reassoc] theorem j₀_str : j₀ X ≫ X.E₀.L.schemeKerStr N = X.E₀.lev ≫ X.E₀.f := kerLift_str _ _ _ _

scoped instance isClosedImmersion_j₀ : IsClosedImmersion (j₀ X) := by
  haveI : IsClosedImmersion (j₀ X ≫ kerι X.E₀.L N) := by rw [j₀_kerι]; exact X.E₀.lev_closed
  haveI : IsSeparated X.E₀.f := by haveI := X.E₀.bundle.proper; infer_instance
  haveI := isClosedImmersion_kerι X.E₀.L N
  exact IsClosedImmersion.of_comp (j₀ X) (kerι X.E₀.L N)

theorem isOpenImmersion_j₀ : IsOpenImmersion (j₀ X) := by
  have hN₀ := isUnit_S₀ X
  obtain ⟨-, X.het⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit X.E₀ N hN₀
  haveI := X.het
  haveI : IsSeparated X.E₀.f := by haveI := X.E₀.bundle.proper; infer_instance
  haveI := isClosedImmersion_kerι X.E₀.L N
  haveI : IsClosedImmersion (j₀ X) := by
    haveI : IsClosedImmersion (j₀ X ≫ kerι X.E₀.L N) := by rw [j₀_kerι]; exact X.E₀.lev_closed
    exact IsClosedImmersion.of_comp (j₀ X) (kerι X.E₀.L N)
  haveI : Etale (X.E₀.lev ≫ X.E₀.f) := by
    haveI : FormallyUnramified (X.E₀.lev ≫ X.E₀.f) := by
      rw [← j₀_str]
      exact MorphismProperty.comp_mem _ _ _ (inferInstance : FormallyUnramified (j₀ X))
        (inferInstance : FormallyUnramified (X.E₀.L.schemeKerStr N))
    haveI := X.E₀.lev_flat
    haveI := X.E₀.lev_finitePresentation
    exact Etale.of_formallyUnramified_of_flat _
  haveI : Etale (j₀ X ≫ X.E₀.L.schemeKerStr N) := by rw [j₀_str]; infer_instance
  haveI : Etale (j₀ X) := Etale.of_comp (j₀ X) (X.E₀.L.schemeKerStr N)
  exact IsOpenImmersion.of_flat_of_mono _

def tautK₀ : SchemeHomOver (X.E₀.L.schemeKerStr N) X.E₀.f := ⟨kerι X.E₀.L N, kerι_f _ _⟩

theorem tautK₀_torsion : nsmulPt X.E₀.L _ N (tautK₀ X) = X.E₀.L.one _ :=
  nsmulPt_eq_one_of_comp_kerι X.E₀.L N _ (𝟙 _) (Category.id_comp _)

def gK : X.E₀.L.schemeKer N ⟶ X.L.schemeKer N :=
  kerLift X.L N (gPt X (tautK₀ X))
    (by rw [← (gPt_one_inv_nsmulPt X _).2.2, tautK₀_torsion X, (gPt_one_inv_nsmulPt X _).1])

@[reassoc] theorem gK_kerι : gK X ≫ kerι X.L N = kerι X.E₀.L N ≫ X.g := kerLift_kerι _ _ _ _

@[reassoc] theorem gK_str :
    gK X ≫ X.L.schemeKerStr N = X.E₀.L.schemeKerStr N ≫ Spec.map (CommRingCat.ofHom X.p) :=
  kerLift_str _ _ _ _

theorem isPullback_gK : IsPullback (gK X) (kerι X.E₀.L N) (kerι X.L N) X.g := by
  haveI : IsSeparated X.E₀.f := by haveI := X.E₀.bundle.proper; infer_instance
  haveI := isClosedImmersion_kerι X.E₀.L N
  refine IsPullback.of_isLimit' ⟨gK_kerι X⟩ (PullbackCone.IsLimit.mk _ (fun s => ?_) (fun s => ?_)
    (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  ·
    let v : SchemeHomOver (s.snd ≫ X.E₀.f) X.E₀.f := ⟨s.snd, rfl⟩
    have hv : nsmulPt X.E₀.L _ N v = X.E₀.L.one _ := by
      rw [← nsmulPt_gPt_eq_one_iff X]
      exact nsmulPt_eq_one_of_comp_kerι X.L N _ s.fst (by simp [gPt_coe, v, s.condition])
    exact kerLift X.E₀.L N v hv
  ·
    haveI := isClosedImmersion_kerι X.L N
    apply Mono.right_cancellation (f := kerι X.L N)
    rw [Category.assoc, gK_kerι, kerLift_kerι_assoc]
    exact s.condition.symm
  · exact kerLift_kerι _ _ _ _
  · apply Mono.right_cancellation (f := kerι X.E₀.L N)
    rw [hm₂, kerLift_kerι]

theorem isClosedImmersion_gK : IsClosedImmersion (gK X) := by
  haveI : IsClosedImmersion X.g :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback X.hg.flip (isClosedImmersion_specMap X.p X.hp)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_gK X).flip ‹_›

theorem surjective_gK : Surjective (gK X) := by
  haveI : Surjective X.g :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback X.hg.flip (surjective_specMap X.p X.hp X.hI)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_gK X).flip ‹_›

theorem isHomeomorph_gK : IsHomeomorph (gK X).base := by
  haveI := isClosedImmersion_gK X
  haveI := surjective_gK X
  rw [isHomeomorph_iff_isEmbedding_surjective]
  exact ⟨(gK X).isClosedEmbedding.isEmbedding, (gK X).surjective⟩

def U : (X.L.schemeKer N).Opens :=
  ⟨(gK X).base '' Set.range (j₀ X).base, by
    haveI := isOpenImmersion_j₀ X
    exact (isHomeomorph_gK X).isOpenMap _ (j₀ X).isOpenEmbedding.isOpen_range⟩

theorem isClosed_U : IsClosed ((U X : (X.L.schemeKer N).Opens) : Set (X.L.schemeKer N)) := by
  haveI := isClosedImmersion_gK X
  exact (gK X).isClosedEmbedding.isClosedMap _ (j₀ X).isClosedEmbedding.isClosed_range

private def _root_.LevLiftExistsBody.lev : ((U X : (X.L.schemeKer N).Opens) : Scheme.{0}) ⟶ X.A :=
  (U X).ι ≫ kerι X.L N

p2m_export "LevLiftExistsBody" "lev"
theorem lev_f : lev X ≫ X.f = (U X).ι ≫ X.L.schemeKerStr N := by
  rw [lev, Category.assoc, kerι_f]

scoped instance isClosedImmersion_Uι : IsClosedImmersion (U X).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact isClosed_U X)

theorem isClosedImmersion_lev : IsClosedImmersion (lev X) := by
  haveI := isClosedImmersion_kerι X.L N
  rw [lev]; infer_instance

theorem isFinite_and_etale_lev_f :
    IsFinite (lev X ≫ X.f) ∧ Etale (lev X ≫ X.f) := by
  rw [lev_f]
  haveI := X.hfin; haveI := X.het
  exact AlgebraicGeometry.isFinite_and_etale_comp_of_isOpenImmersion_of_isClosed_range _
    (by rw [Scheme.Opens.range_ι]; exact isClosed_U X) _

theorem image_U_eq : (kerι X.L N).base '' ((U X : (X.L.schemeKer N).Opens) : Set (X.L.schemeKer N)) =
    Set.range (X.E₀.lev ≫ X.g).base := by
  show (kerι X.L N).base '' ((gK X).base '' Set.range (j₀ X).base) = _
  rw [Set.image_image, ← Set.range_comp]
  congr 1
  funext x
  show ((j₀ X ≫ gK X) ≫ kerι X.L N).base x = (X.E₀.lev ≫ X.g).base x
  rw [Category.assoc, gK_kerι, ← Category.assoc, j₀_kerι]

theorem range_lev : Set.range (lev X).base = Set.range (X.E₀.lev ≫ X.g).base := by
  rw [← image_U_eq X, lev, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Scheme.Opens.range_ι]

theorem factorsThrough_lev_iff {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t X.f) :
    FactorsThrough (lev X) P ↔
      nsmulPt X.L t N P = X.L.one t ∧ Set.range P.1.base ⊆ Set.range (X.E₀.lev ≫ X.g).base := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨nsmulPt_eq_one_of_comp_kerι X.L N P (Q ≫ (U X).ι) (by rw [Category.assoc]; exact hQ), ?_⟩
    rw [← range_lev X, ← hQ, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  · rintro ⟨htor, hrange⟩
    let P' := kerLift X.L N P htor
    have hP' : Set.range P'.base ⊆ Set.range (U X).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      have hx : (kerι X.L N).base (P'.base x) ∈ Set.range (X.E₀.lev ≫ X.g).base := by
        apply hrange
        refine ⟨x, ?_⟩
        rw [← Scheme.Hom.comp_apply, kerLift_kerι]
      rw [← image_U_eq X] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      haveI := isClosedImmersion_kerι X.L N
      rwa [← (kerι X.L N).isClosedEmbedding.injective hxy]
    refine ⟨IsOpenImmersion.lift _ P' hP', ?_⟩
    rw [lev, ← Category.assoc, IsOpenImmersion.lift_fac, kerLift_kerι]

theorem factorsThrough_lev₀_iff {T : Scheme.{0}} (t₀ : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t₀ X.E₀.f) :
    FactorsThrough X.E₀.lev P ↔ nsmulPt X.E₀.L t₀ N P = X.E₀.L.one t₀ ∧ Set.range P.1.base ⊆ Set.range X.E₀.lev.base := by
  constructor
  · rintro hP
    refine ⟨X.E₀.lev_torsion t₀ P hP, ?_⟩
    obtain ⟨Q, hQ⟩ := hP
    rw [← hQ, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  · rintro ⟨htor, hrange⟩
    haveI := isOpenImmersion_j₀ X
    let P' := kerLift X.E₀.L N P htor
    have hP' : Set.range P'.base ⊆ Set.range (j₀ X).base := by
      rintro _ ⟨x, rfl⟩
      have hx : (kerι X.E₀.L N).base (P'.base x) ∈ Set.range X.E₀.lev.base := by
        apply hrange
        refine ⟨x, ?_⟩
        rw [← Scheme.Hom.comp_apply, kerLift_kerι]
      obtain ⟨c, hc⟩ := hx
      refine ⟨c, ?_⟩
      haveI : IsSeparated X.E₀.f := by haveI := X.E₀.bundle.proper; infer_instance
      haveI := isClosedImmersion_kerι X.E₀.L N
      apply (kerι X.E₀.L N).isClosedEmbedding.injective
      rw [← hc, ← Scheme.Hom.comp_apply, j₀_kerι]
    refine ⟨IsOpenImmersion.lift _ P' hP', ?_⟩
    rw [← j₀_kerι X, ← Category.assoc, IsOpenImmersion.lift_fac, kerLift_kerι]

theorem factorsThrough_iff_gPt {T : Scheme.{0}} (t₀ : T ⟶ Spec (CommRingCat.of S₀)) (P₀ : SchemeHomOver t₀ X.E₀.f) :
    FactorsThrough X.E₀.lev P₀ ↔ FactorsThrough (lev X) (gPt X P₀) := by
  rw [factorsThrough_lev_iff, factorsThrough_lev₀_iff X, nsmulPt_gPt_eq_one_iff X]
  haveI : IsClosedImmersion X.g :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback X.hg.flip (isClosedImmersion_specMap X.p X.hp)
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · rw [gPt_coe, Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.coe_comp, TopCat.coe_comp, Set.range_comp,
      Set.range_comp]
    exact Set.image_mono h
  · rintro _ ⟨x, rfl⟩
    have hx : X.g.base (P₀.1.base x) ∈ Set.range (X.E₀.lev ≫ X.g).base := h ⟨x, by rw [gPt_coe, Scheme.Hom.comp_apply]⟩
    obtain ⟨c, hc⟩ := hx
    exact ⟨c, X.g.isClosedEmbedding.injective (by rwa [Scheme.Hom.comp_apply] at hc)⟩

theorem lev_iff {T : Scheme.{0}} (t₀ : T ⟶ Spec (CommRingCat.of S₀)) (P₀ : SchemeHomOver t₀ X.E₀.f) :
    FactorsThrough X.E₀.lev P₀ ↔ ∃ Q : T ⟶ _, Q ≫ lev X = P₀.1 ≫ X.g :=
  factorsThrough_iff_gPt X t₀ P₀

private theorem _root_.LevLiftExistsBody.lev_torsion {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t X.f)
    (hP : FactorsThrough (lev X) P) : nsmulPt X.L t N P = X.L.one t :=
  ((factorsThrough_lev_iff X t P).mp hP).1

p2m_export "LevLiftExistsBody" "lev_torsion"

theorem factorsThrough_of_forall_residue {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t X.f)
    (htor : nsmulPt X.L t N P = X.L.one t)
    (h : ∀ x : T, FactorsThrough (lev X)
      (schemeHomOverComp (T.fromSpecResidueField x) rfl P : SchemeHomOver (T.fromSpecResidueField x ≫ t) X.f)) :
    FactorsThrough (lev X) P := by
  rw [factorsThrough_lev_iff]
  refine ⟨htor, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx := ((factorsThrough_lev_iff X _ _).mp (h x)).2
  have : P.1.base x = (T.fromSpecResidueField x ≫ P.1).base (IsLocalRing.closedPoint _) := by
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  rw [this]
  exact hx ⟨_, rfl⟩

theorem exists_residue_base {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : T) :
    ∃ t₀ : Spec (CommRingCat.of (T.residueField x)) ⟶ Spec (CommRingCat.of S₀),
      T.fromSpecResidueField x ≫ t = t₀ ≫ Spec.map (CommRingCat.ofHom X.p) :=
  exists_eq_comp_specMap X.p X.hp X.hI _

private theorem _root_.LevLiftExistsBody.lev_sub (hcomm : X.L.IsCommutative) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t X.f)
    (hP : FactorsThrough (lev X) P) (hQ : FactorsThrough (lev X) Q) :
    FactorsThrough (lev X) (X.L.mul t P Q) ∧
      FactorsThrough (lev X) (X.L.inv t P) := by
  have hPt := lev_torsion X t P hP
  have hQt := lev_torsion X t Q hQ
  obtain ⟨hmult, hinvt⟩ := nsmulPt_mul_inv_eq_one X.L hcomm t N P Q hPt hQt

  have key : ∀ x : T,
      FactorsThrough (lev X)
          (schemeHomOverComp (T.fromSpecResidueField x) rfl (X.L.mul t P Q) :
            SchemeHomOver (T.fromSpecResidueField x ≫ t) X.f) ∧
        FactorsThrough (lev X)
          (schemeHomOverComp (T.fromSpecResidueField x) rfl (X.L.inv t P) :
            SchemeHomOver (T.fromSpecResidueField x ≫ t) X.f) := by
    intro x
    obtain ⟨t₀, ht₀⟩ := exists_residue_base X t x
    let τ := T.fromSpecResidueField x

    let P' : SchemeHomOver (t₀ ≫ Spec.map (CommRingCat.ofHom X.p)) X.f := schemeHomOverComp τ ht₀ P
    let Q' : SchemeHomOver (t₀ ≫ Spec.map (CommRingCat.ofHom X.p)) X.f := schemeHomOverComp τ ht₀ Q
    have hP' : FactorsThrough (lev X) P' := by
      obtain ⟨R, hR⟩ := hP; exact ⟨τ ≫ R, by rw [Category.assoc, hR]; rfl⟩
    have hQ' : FactorsThrough (lev X) Q' := by
      obtain ⟨R, hR⟩ := hQ; exact ⟨τ ≫ R, by rw [Category.assoc, hR]; rfl⟩

    have hlP : FactorsThrough X.E₀.lev (liftPt X P') := by
      rw [factorsThrough_iff_gPt X, gPt_liftPt]; exact hP'
    have hlQ : FactorsThrough X.E₀.lev (liftPt X Q') := by
      rw [factorsThrough_iff_gPt X, gPt_liftPt]; exact hQ'
    obtain ⟨hm₀, hi₀⟩ := X.E₀.lev_sub t₀ _ _ hlP hlQ
    rw [factorsThrough_iff_gPt X] at hm₀ hi₀
    rw [gPt_mul X, gPt_liftPt, gPt_liftPt] at hm₀
    rw [(gPt_one_inv_nsmulPt X t₀).2.1, gPt_liftPt] at hi₀

    have hmn : X.L.mul _ P' Q' = schemeHomOverComp τ ht₀ (X.L.mul t P Q) := (X.L.mul_natural t _ τ ht₀ P Q).symm
    have hin : X.L.inv _ P' = schemeHomOverComp τ ht₀ (X.L.inv t P) := (inv_natural X.L t _ τ ht₀ P).symm
    rw [hmn] at hm₀
    rw [hin] at hi₀

    obtain ⟨R₁, hR₁⟩ := hm₀
    obtain ⟨R₂, hR₂⟩ := hi₀
    exact ⟨⟨R₁, hR₁⟩, ⟨R₂, hR₂⟩⟩
  exact ⟨factorsThrough_of_forall_residue X t _ hmult (fun x => (key x).1),
    factorsThrough_of_forall_residue X t _ hinvt (fun x => (key x).2)⟩

p2m_export "LevLiftExistsBody" "lev_sub"

private theorem _root_.LevLiftExistsBody.lev_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    FactorsThrough (lev X) (X.L.one t) := by
  apply factorsThrough_of_forall_residue X t _ (nsmulPt_one X.L t N)
  intro x
  obtain ⟨t₀, ht₀⟩ := exists_residue_base X t x
  have h1 : FactorsThrough (lev X)
      (schemeHomOverComp (T.fromSpecResidueField x) ht₀ (X.L.one t)) := by
    rw [X.L.one_natural t _ _ ht₀, ← (gPt_one_inv_nsmulPt X t₀).1,
      ← factorsThrough_iff_gPt X]
    exact X.E₀.lev_one t₀
  obtain ⟨R, hR⟩ := h1
  exact ⟨R, hR⟩

p2m_export "LevLiftExistsBody" "lev_one"

theorem lev_stable (α : X.A ⟶ X.A) (hα : α ≫ X.f = X.f)
    (hαmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t X.f),
      pushPt α hα (X.L.mul t P Q) = X.L.mul t (pushPt α hα P) (pushPt α hα Q))
    (β : X.E₀.A ⟶ X.E₀.A) (hβ : β ≫ X.E₀.f = X.E₀.f) (hβg : β ≫ X.g = X.g ≫ α)
    (hβstab : ∀ {T : Scheme.{0}} (t₀ : T ⟶ Spec (CommRingCat.of S₀)) (P₀ : SchemeHomOver t₀ X.E₀.f),
      FactorsThrough X.E₀.lev P₀ → FactorsThrough X.E₀.lev (pushPt β hβ P₀))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t X.f)
    (hP : FactorsThrough (lev X) P) :
    FactorsThrough (lev X) (pushPt α hα P) := by
  rw [factorsThrough_lev_iff] at hP ⊢
  obtain ⟨htor, hrange⟩ := hP
  obtain ⟨h1, -, hn⟩ := map_one_inv_nsmulPt X.L X.L t t (pushPt α hα) (hαmul t)
  refine ⟨by rw [← hn, htor, h1], ?_⟩

  have hZ : α.base '' Set.range (X.E₀.lev ≫ X.g).base ⊆ Set.range (X.E₀.lev ≫ X.g).base := by
    obtain ⟨c, hc⟩ := hβstab (X.E₀.lev ≫ X.E₀.f) ⟨X.E₀.lev, rfl⟩ ⟨𝟙 _, Category.id_comp _⟩

    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    refine ⟨c.base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    have : (X.E₀.lev ≫ X.g) ≫ α = c ≫ X.E₀.lev ≫ X.g := by
      rw [Category.assoc, ← hβg, ← Category.assoc, ← Category.assoc, hc]; rfl
    rw [this]
  refine subset_trans ?_ hZ
  rintro _ ⟨x, rfl⟩
  exact ⟨P.1.base x, hrange ⟨x, rfl⟩, by rw [mapPt_coe, Scheme.Hom.comp_apply]⟩

def gC : X.E₀.C ⟶ ((U X : (X.L.schemeKer N).Opens) : Scheme.{0}) :=
  IsOpenImmersion.lift (U X).ι (j₀ X ≫ gK X)
    (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨c, rfl⟩
      exact ⟨(j₀ X).base c, ⟨c, rfl⟩, by rw [Scheme.Hom.comp_apply]⟩)

@[reassoc] theorem gC_ι : gC X ≫ (U X).ι = j₀ X ≫ gK X :=
  IsOpenImmersion.lift_fac _ _ _

theorem isPullback_gC :
    IsPullback (gC X) (j₀ X) (U X).ι (gK X) := by
  haveI := isOpenImmersion_j₀ X
  haveI := isClosedImmersion_gK X
  refine IsPullback.of_isLimit' ⟨gC_ι X⟩ (PullbackCone.IsLimit.mk _ (fun s => ?_) (fun s => ?_)
    (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  ·
    refine IsOpenImmersion.lift (j₀ X) s.snd ?_
    rintro _ ⟨x, rfl⟩
    have hx : (gK X).base (s.snd.base x) ∈
        ((U X : (X.L.schemeKer N).Opens) : Set (X.L.schemeKer N)) := by
      rw [← Scheme.Hom.comp_apply, ← s.condition, Scheme.Hom.comp_apply]
      exact (s.fst.base x).2
    obtain ⟨y, hy, hxy⟩ := hx
    rwa [← (gK X).isClosedEmbedding.injective hxy]
  · apply Mono.right_cancellation (f := (U X).ι)
    rw [Category.assoc, gC_ι, IsOpenImmersion.lift_fac_assoc]
    exact s.condition.symm
  · exact IsOpenImmersion.lift_fac _ _ _
  · apply Mono.right_cancellation (f := j₀ X)
    rw [hm₂, IsOpenImmersion.lift_fac]

private theorem _root_.LevLiftExistsBody.lev_rank (s : ↥(Spec (CommRingCat.of S))) : (lev X ≫ X.f).finrank s = N ^ 2 := by

  have hsq : IsPullback (gC X) (j₀ X ≫ kerι X.E₀.L N ≫ X.E₀.f)
      ((U X).ι ≫ kerι X.L N ≫ X.f) (Spec.map (CommRingCat.ofHom X.p)) :=
    (isPullback_gC X).paste_vert ((isPullback_gK X).paste_vert X.hg)
  have h1 : j₀ X ≫ kerι X.E₀.L N ≫ X.E₀.f = X.E₀.lev ≫ X.E₀.f := by rw [← Category.assoc, j₀_kerι]
  have h2 : (U X).ι ≫ kerι X.L N ≫ X.f = lev X ≫ X.f := by
    rw [← Category.assoc]; rfl
  rw [h1, h2] at hsq
  obtain ⟨hfin', het'⟩ := isFinite_and_etale_lev_f X
  haveI := hfin'; haveI := het'
  haveI := surjective_specMap X.p X.hp X.hI
  obtain ⟨s₀, rfl⟩ := (Spec.map (CommRingCat.ofHom X.p)).surjective s
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq s₀]
  exact X.E₀.lev_rank s₀

p2m_export "LevLiftExistsBody" "lev_rank"

private theorem _root_.LevLiftExistsBody.lev_fibre (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (hNk : (N : k) ≠ 0) :
    ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) X.f // FactorsThrough (lev X) P},
      ∀ x y : ZMod N × ZMod N,
        (e (x + y) : SchemeHomOver (geomPoint k sk) X.f) = X.L.mul (geomPoint k sk) (e x) (e y) := by
  obtain ⟨sk₀, hsk⟩ := exists_eq_comp X.p X.hp X.hI sk
  have hb : geomPoint k sk = geomPoint k sk₀ ≫ Spec.map (CommRingCat.ofHom X.p) := by
    unfold geomPoint; rw [hsk, CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨e₀, he₀⟩ := X.E₀.lev_fibre k sk₀ hNk

  let cast : SchemeHomOver (geomPoint k sk) X.f → SchemeHomOver (geomPoint k sk₀ ≫ Spec.map (CommRingCat.ofHom X.p)) X.f :=
    fun P => ⟨P.1, P.2.trans hb⟩
  let uncast : SchemeHomOver (geomPoint k sk₀ ≫ Spec.map (CommRingCat.ofHom X.p)) X.f → SchemeHomOver (geomPoint k sk) X.f :=
    fun P => ⟨P.1, P.2.trans hb.symm⟩
  have hmulcast : ∀ P Q, X.L.mul _ (cast P) (cast Q) = cast (X.L.mul _ P Q) := fun P Q =>
    Subtype.ext (coe_mul_cast X.L hb P Q)
  have hinj := gPt_injective X (geomPoint k sk₀) (T := Spec (CommRingCat.of k))
  let Ψ : {P : SchemeHomOver (geomPoint k sk) X.f // FactorsThrough (lev X) P} ≃
      {P₀ : SchemeHomOver (geomPoint k sk₀) X.E₀.f // FactorsThrough X.E₀.lev P₀} :=
    { toFun := fun P => ⟨liftPt X (cast P.1), by
        rw [factorsThrough_iff_gPt X, gPt_liftPt]
        obtain ⟨R, hR⟩ := P.2; exact ⟨R, hR⟩⟩
      invFun := fun P₀ => ⟨uncast (gPt X P₀.1), by
        have := (factorsThrough_iff_gPt X _ P₀.1).mp P₀.2
        obtain ⟨R, hR⟩ := this; exact ⟨R, hR⟩⟩
      left_inv := fun P => by
        apply Subtype.ext; apply Subtype.ext
        show (gPt X (liftPt X (cast P.1))).1 = P.1.1
        rw [gPt_liftPt]
      right_inv := fun P₀ => by
        apply Subtype.ext
        show liftPt X (cast (uncast (gPt X P₀.1))) = P₀.1
        have : cast (uncast (gPt X P₀.1)) = gPt X P₀.1 := Subtype.ext rfl
        rw [this, liftPt_gPt X _ hinj] }
  refine ⟨e₀.trans Ψ.symm, fun x y => ?_⟩
  show (uncast (gPt X (e₀ (x + y)).1)) = X.L.mul _ (uncast (gPt X (e₀ x).1)) (uncast (gPt X (e₀ y).1))
  apply Subtype.ext
  show ((e₀ (x + y) : SchemeHomOver (geomPoint k sk₀) X.E₀.f).1 ≫ X.g) = _
  rw [he₀ x y, ← gPt_coe X, gPt_mul X]
  have : ∀ P Q : SchemeHomOver (geomPoint k sk₀ ≫ Spec.map (CommRingCat.ofHom X.p)) X.f,
      (X.L.mul _ P Q).1 = (X.L.mul (geomPoint k sk) (uncast P) (uncast Q)).1 := by
    intro P Q
    have hP : P = cast (uncast P) := Subtype.ext rfl
    have hQ : Q = cast (uncast Q) := Subtype.ext rfl
    conv_lhs => rw [hP, hQ, hmulcast]
  exact this _ _

p2m_export "LevLiftExistsBody" "lev_fibre"
end Main

end LevLiftExistsBody
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_lev_finrank_eq_sq_forall_factorsThrough_iff_of_isPullback_of_isNilpotent_ker.LevLiftExistsBody"

open LevLiftExistsBody in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S₀ : Type} [CommRing S] [CommRing S₀]
    (p : S →+* S₀) (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    (E₀ : FakeEllipticCurve Λ N S₀)
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} [IsSeparated f]
    (L : RelativeGroupLaw S f) (hcomm : L.IsCommutative)
    (hN : IsUnit ((N : ℕ) : S))
    (hfin : IsFinite (L.schemeKerStr N)) (het : Etale (L.schemeKerStr N))
    (g : E₀.A ⟶ A) (hg : CategoryTheory.IsPullback g E₀.f f (Spec.map (CommRingCat.ofHom p)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom p))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) :
    ∃ (C : Scheme.{0}) (lev : C ⟶ A),
      IsClosedImmersion lev ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
        FactorsThrough lev P → FactorsThrough lev Q →
          FactorsThrough lev (L.mul t P Q) ∧ FactorsThrough lev (L.inv t P)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)), FactorsThrough lev (L.one t)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
        FactorsThrough lev P → nsmulPt L t N P = L.one t) ∧
      IsFinite (lev ≫ f) ∧ Flat (lev ≫ f) ∧ LocallyOfFinitePresentation (lev ≫ f) ∧
      (∀ s : ↥(Spec (CommRingCat.of S)), (lev ≫ f).finrank s = N ^ 2) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), (N : k) ≠ 0 →
        ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough lev P},
          ∀ x y : ZMod N × ZMod N,
            (e (x + y) : SchemeHomOver (geomPoint k sk) f) = L.mul (geomPoint k sk) (e x) (e y)) ∧
      (∀ {T : Scheme.{0}} (t₀ : T ⟶ Spec (CommRingCat.of S₀)) (P₀ : SchemeHomOver t₀ E₀.f),
        FactorsThrough E₀.lev P₀ ↔ ∃ Q : T ⟶ C, Q ≫ lev = P₀.1 ≫ g) ∧
      (∀ (α : A ⟶ A) (hα : α ≫ f = f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
          pushPt α hα (L.mul t P Q) = L.mul t (pushPt α hα P) (pushPt α hα Q)) →
        ∀ (β : E₀.A ⟶ E₀.A) (hβ : β ≫ E₀.f = E₀.f), β ≫ g = g ≫ α →
        (∀ {T : Scheme.{0}} (t₀ : T ⟶ Spec (CommRingCat.of S₀)) (P₀ : SchemeHomOver t₀ E₀.f),
          FactorsThrough E₀.lev P₀ → FactorsThrough E₀.lev (pushPt β hβ P₀)) →
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
          FactorsThrough lev P → FactorsThrough lev (pushPt α hα P)) := by
  let X : LevLiftExistsBody.Setup Λ N S S₀ :=
    { p := p, hp := hp, hI := hI, E₀ := E₀, A := A, f := f, sep := inferInstance, L := L, hN := hN, hfin := hfin,
      het := het, g := g, hg := hg, hmul := fun t' P Q => hmul t' P Q }
  obtain ⟨hfin', het'⟩ := isFinite_and_etale_lev_f X
  haveI := het'
  refine ⟨_, LevLiftExistsBody.lev X, isClosedImmersion_lev X,
    fun t P Q hP hQ => lev_sub X hcomm t P Q hP hQ,
    fun t => lev_one X t,
    fun t P hP => lev_torsion X t P hP,
    hfin', inferInstance, inferInstance,
    fun s => lev_rank X s,
    fun k _ _ sk hNk => lev_fibre X k sk hNk,
    fun t₀ P₀ => lev_iff X t₀ P₀,
    fun α hα hαmul β hβ hβg hβstab T t P hP => lev_stable X α hα hαmul β hβ hβg hβstab t P hP⟩

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_lev_finrank_eq_sq_forall_factorsThrough_iff_of_isPullback_of_isNilpotent_ker.LevLiftExistsBody"

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_lev_finrank_eq_sq_forall_factorsThrough_iff_of_isPullback_of_isNilpotent_ker
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_lev_finrank_eq_sq_forall_factorsThrough_iff_of_isPullback_of_isNilpotent_ker (solution)
