-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_factorsThrough_mapPt_relFrobenius_eq_of_not_dvd_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/660d330c-a71d-5e7b-95e2-082396730651

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isReduced_C_of_natCast_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_factorsThrough_mapPt_relFrobenius_eq_of_not_dvd_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace B12LevelEtale

theorem natCast_eq_zero_of_over {p : ℕ} {k : Type u} [CommRing k] (hk : (p : k) = 0)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : (p : Γ(T, ⊤)) = 0 := by
  have h0 : (p : Γ(Spec (CommRingCat.of k), ⊤)) = 0 := Scheme.natCast_eq_zero_ΓSpec hk
  have := congrArg (fun s => t.appTop.hom s) h0
  simpa using this

theorem frobenius_Spec_eq {p : ℕ} [hp : Fact p.Prime] (k : Type u) [CommRing k] [CharP k p]
    (h : (p : Γ(Spec (CommRingCat.of k), ⊤)) = 0) :
    (Spec (CommRingCat.of k)).frobenius p 1 hp.out h = Spec.map (CommRingCat.ofHom (frobenius k p)) := by
  have e : powCharRingHom k p 1 hp.out (CharP.cast_eq_zero k p) = frobenius k p := by
    ext x; simp [powCharRingHom_apply, frobenius_def]
  rw [← e]
  exact Scheme.frobenius_Spec p 1 hp.out (CharP.cast_eq_zero k p)

theorem frobenius_comp_over {p : ℕ} [hp : Fact p.Prime] {k : Type u} [CommRing k] [CharP k p]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (hT : (p : Γ(T, ⊤)) = 0) :
    T.frobenius p 1 hp.out hT ≫ t = t ≫ Spec.map (CommRingCat.ofHom (frobenius k p)) := by
  rw [Scheme.frobenius_comp t p 1 hp.out hT (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero k p)),
    frobenius_Spec_eq]

theorem bijective_powCharRingHom {K : Type*} [Field K] [IsAlgClosed K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (R : Type*) [CommRing R] [Algebra K R] [Module.Finite K R] [IsReduced R] (hR : (p : R) = 0) :
    Function.Bijective (powCharRingHom R p 1 hp.out hR) := by
  constructor
  · intro x y hxy
    rw [← sub_eq_zero]
    apply IsReduced.eq_zero
    refine ⟨p ^ 1, ?_⟩
    rw [← powCharRingHom_apply p 1 hp.out hR, map_sub, hxy, sub_self]
  · haveI : IsArtinianRing R := IsArtinianRing.of_finite K R
    let e := IsArtinianRing.equivPi R
    intro y
    have hfac : ∀ (I : MaximalSpectrum R) (z : R ⧸ I.asIdeal), ∃ w : R ⧸ I.asIdeal, w ^ p = z := by
      intro I z
      haveI : I.asIdeal.IsMaximal := I.isMaximal
      haveI : Module.Finite K (R ⧸ I.asIdeal) :=
        Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap (Ideal.Quotient.mkₐ_surjective K _)
      haveI : Algebra.IsIntegral K (R ⧸ I.asIdeal) := Algebra.IsIntegral.of_finite K _
      obtain ⟨c, rfl⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := R ⧸ I.asIdeal)).2 z
      obtain ⟨d, rfl⟩ := (PerfectRing.bijective_frobenius (R := K) (p := p)).2 c
      exact ⟨algebraMap K _ d, by rw [← map_pow]⟩
    choose w hw using fun I => hfac I (e y I)
    refine ⟨e.symm (fun I => w I), ?_⟩
    rw [powCharRingHom_apply, pow_one]
    apply e.injective
    rw [map_pow, AlgEquiv.apply_symm_apply]
    funext I
    rw [Pi.pow_apply, hw]

theorem isIso_frobenius_of_isFinite {K : Type u} [Field K] [IsAlgClosed K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsFinite c] [IsReduced C] (hC : (p : Γ(C, ⊤)) = 0) :
    IsIso (C.frobenius p 1 hp.out hC) := by
  haveI : IsAffine C := isAffine_of_isAffineHom c
  let φ : K →+* Γ(C, ⊤) := (c.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  letI : Algebra K Γ(C, ⊤) := φ.toAlgebra
  haveI : Module.Finite K Γ(C, ⊤) := by
    have h1 : (c.appTop).hom.Finite := IsFinite.finite_app c ⊤ (isAffineOpen_top _)
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
    exact RingHom.Finite.comp h1 h2
  have hbij := bijective_powCharRingHom (K := K) p Γ(C, ⊤) hC
  have hΓ : (p : Γ(Spec Γ(C, ⊤), ⊤)) = 0 := Scheme.natCast_eq_zero_ΓSpec hC
  haveI hiso : IsIso ((Spec Γ(C, ⊤)).frobenius p 1 hp.out hΓ) :=
    Scheme.isIso_frobenius_Spec_of_bijective p 1 hp.out hC hbij
  have hcomm := Scheme.frobenius_comp C.isoSpec.hom p 1 hp.out hC hΓ
  have e : C.frobenius p 1 hp.out hC = C.isoSpec.hom ≫ (Spec Γ(C, ⊤)).frobenius p 1 hp.out hΓ ≫ C.isoSpec.inv := by
    rw [← Category.assoc, ← hcomm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]; infer_instance

end B12LevelEtale

open B12LevelEtale

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [CharP k ℓ]
    (E Eℓ : FakeEllipticCurve Λ N k)
    (pr : Eℓ.A ⟶ E.A)
    (pr_isPullback : CategoryTheory.IsPullback pr Eℓ.f E.f (Spec.map (CommRingCat.ofHom (frobenius k ℓ))))
    (pr_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t' Eℓ.f),
      (Eℓ.L.mul t' P Q).1 ≫ pr =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (frobenius k ℓ)))
          ⟨P.1 ≫ pr, by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pr, by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, Q.2]⟩).1)
    (pr_act : ∀ x : ↥Λ, Eℓ.act x ≫ pr = pr ≫ E.act x)
    (pr_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t' Eℓ.f),
      FactorsThrough Eℓ.lev P → ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ pr)
    (pr_lev' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t' Eℓ.f),
      (∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ pr) → FactorsThrough Eℓ.lev P)
    (hA : (ℓ : Γ(E.A, ⊤)) = 0)
    (F : E.A ⟶ Eℓ.A) (F_over : F ≫ Eℓ.f = E.f) (F_pr : F ≫ pr = E.A.frobenius ℓ 1 hℓ.out hA)
    (F_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt F F_over (E.L.mul t P Q) = Eℓ.L.mul t (mapPt F F_over P) (mapPt F F_over Q))
    (hℓN : ¬ ℓ ∣ N)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t Eℓ.f) (hQ : FactorsThrough Eℓ.lev Q) :
    ∃! P : SchemeHomOver t E.f, FactorsThrough E.lev P ∧ mapPt F F_over P = Q := by
  have hk0 : ((ℓ : ℕ) : k) = 0 := CharP.cast_eq_zero k ℓ
  have hNk : (N : k) ≠ 0 := fun h => hℓN ((CharP.cast_eq_zero_iff k ℓ N).mp h)
  haveI : IsReduced E.C := CerednikDrinfeld.QM.FakeEllipticCurve.isReduced_C_of_natCast_ne_zero k E hNk
  haveI : IsFinite (E.lev ≫ E.f) := E.lev_finite
  haveI : IsClosedImmersion E.lev := E.lev_closed
  have hC : (ℓ : Γ(E.C, ⊤)) = 0 := natCast_eq_zero_of_over hk0 (E.lev ≫ E.f)
  haveI hΦC : IsIso (E.C.frobenius ℓ 1 hℓ.out hC) := isIso_frobenius_of_isFinite ℓ (E.lev ≫ E.f) hC
  haveI hFk : IsIso (Spec.map (CommRingCat.ofHom (frobenius k ℓ))) := by
    haveI : IsIso (CommRingCat.ofHom (frobenius k ℓ)) :=
      (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom (frobenius k ℓ))).2 (bijective_frobenius k ℓ)
    infer_instance

  have hlevΦ : E.C.frobenius ℓ 1 hℓ.out hC ≫ E.lev = E.lev ≫ E.A.frobenius ℓ 1 hℓ.out hA :=
    Scheme.frobenius_comp E.lev ℓ 1 hℓ.out hC hA
  have hcΦ : E.C.frobenius ℓ 1 hℓ.out hC ≫ (E.lev ≫ E.f) = (E.lev ≫ E.f) ≫ Spec.map (CommRingCat.ofHom (frobenius k ℓ)) :=
    frobenius_comp_over (E.lev ≫ E.f) hC

  obtain ⟨Q₀, hQ₀⟩ := pr_lev t Q hQ
  let P₀ : T ⟶ E.C := Q₀ ≫ inv (E.C.frobenius ℓ 1 hℓ.out hC)
  have hP₀ : P₀ ≫ E.C.frobenius ℓ 1 hℓ.out hC = Q₀ := by simp [P₀]
  have hPt : (P₀ ≫ E.lev) ≫ E.f = t := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (frobenius k ℓ)))]
    calc ((P₀ ≫ E.lev) ≫ E.f) ≫ Spec.map (CommRingCat.ofHom (frobenius k ℓ))
        = P₀ ≫ ((E.lev ≫ E.f) ≫ Spec.map (CommRingCat.ofHom (frobenius k ℓ))) := by simp only [Category.assoc]
      _ = P₀ ≫ (E.C.frobenius ℓ 1 hℓ.out hC ≫ (E.lev ≫ E.f)) := by rw [hcΦ]
      _ = Q₀ ≫ E.lev ≫ E.f := by rw [← Category.assoc, hP₀]
      _ = (Q.1 ≫ pr) ≫ E.f := by rw [← Category.assoc, hQ₀]
      _ = Q.1 ≫ Eℓ.f ≫ Spec.map (CommRingCat.ofHom (frobenius k ℓ)) := by rw [Category.assoc, pr_isPullback.w]
      _ = t ≫ Spec.map (CommRingCat.ofHom (frobenius k ℓ)) := by rw [← Category.assoc, Q.2]
  let P : SchemeHomOver t E.f := ⟨P₀ ≫ E.lev, hPt⟩
  have hPF : mapPt F F_over P = Q := by
    apply Subtype.ext
    apply pr_isPullback.hom_ext
    · rw [mapPt_coe, Category.assoc, F_pr]
      change (P₀ ≫ E.lev) ≫ E.A.frobenius ℓ 1 hℓ.out hA = Q.1 ≫ pr
      rw [Category.assoc, ← hlevΦ, ← Category.assoc, hP₀, hQ₀]
    · rw [(mapPt F F_over P).2, Q.2]
  refine ⟨P, ⟨⟨P₀, rfl⟩, hPF⟩, ?_⟩
  rintro P' ⟨⟨P₀', hP₀'⟩, hP'F⟩
  apply Subtype.ext
  have hF' : P'.1 ≫ F = Q.1 := by
    have := congrArg Subtype.val hP'F
    rwa [mapPt_coe] at this

  have hP₀'Φ : P₀' ≫ E.C.frobenius ℓ 1 hℓ.out hC = Q₀ := by
    rw [← cancel_mono E.lev, Category.assoc, hlevΦ, ← Category.assoc, hP₀', ← F_pr, ← Category.assoc, hF', hQ₀]
  have hP₀'eq : P₀' = P₀ := by
    rw [← cancel_mono (E.C.frobenius ℓ 1 hℓ.out hC), hP₀'Φ, hP₀]
  change P'.1 = P₀ ≫ E.lev
  rw [← hP₀', hP₀'eq]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_factorsThrough_mapPt_relFrobenius_eq_of_not_dvd_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_factorsThrough_mapPt_relFrobenius_eq_of_not_dvd_of_isAlgClosed (solution)
