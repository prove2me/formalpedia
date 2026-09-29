-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_symm_of_isAtkinLehnerQuotientVia_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/590757e6-c782-59e4-8f90-b16a42cb6779

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_symm_of_isAtkinLehnerQuotientVia_of_not_dvd

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace DualAL

variable {R : Type} [CommRing R]

@[reducible] def pointCommGroup {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hc : L.IsCommutative) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : CommGroup (SchemeHomOver t f) :=
  { L.pointGroup t with mul_comm := fun x y => hc t x y }

theorem nsmulPt_eq_pow {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    letI := pointCommGroup L hc t
    nsmulPt L t n P = P ^ n := by
  letI := pointCommGroup L hc t
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem eq_one_of_nsmulPt_eq_one_of_coprime {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (hc : L.IsCommutative) {m : ℕ} (hnm : n.Coprime m)
    {P : SchemeHomOver t f} (hn : nsmulPt L t n P = L.one t) (hm : nsmulPt L t m P = L.one t) : P = L.one t := by
  letI := pointCommGroup L hc t
  rw [nsmulPt_eq_pow L hc] at hn hm
  have h1 : orderOf P ∣ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : orderOf P ∣ m := orderOf_dvd_of_pow_eq_one hm
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hnm h1 h2)

theorem eq_one_of_factorsThrough_lev_of_mapPt_eq_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (r : ℕ) [Fact r.Prime] (hrN : ¬ r ∣ N)
    {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f) (q' : E'.A ⟶ E.A) (hq' : q' ≫ E.f = E'.f)
    (h : FakeEllipticCurve.IsAtkinLehnerQuotientVia r E E' q hq q' hq')
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E.f)
    (hQ : FactorsThrough E.lev Q) (h1 : mapPt q hq Q = E'.L.one t) :
    Q = E.L.one t := by
  obtain ⟨-, -, -, -, -, hker, -⟩ := h
  have h1mem : (1 : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ 1
  have hr : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ r

  have hrr : ((⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩ : ↥Λ) : ℍ[ℚ, a, b]) * star ((⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩ : ↥Λ) : ℍ[ℚ, a, b]) =
      ((((r : ℤ) * (r : ℤ) : ℚ)) : ℍ[ℚ, a, b]) := by
    simp only [QuaternionAlgebra.star_coe]
    rw [← QuaternionAlgebra.coe_mul]; push_cast; rfl
  have hrQ : nsmulPt E.L t r Q = E.L.one t := by
    rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E h1mem r hr t Q]
    exact (hker t Q).1 h1 ⟨_, hr⟩ r hrr
  have hNQ : nsmulPt E.L t N Q = E.L.one t := E.lev_torsion t Q hQ
  have hcop : r.Coprime N := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hrN
  exact eq_one_of_nsmulPt_eq_one_of_coprime E.L t r E.comm hcop hrQ hNQ

theorem mapPt_one {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    mapPt φ hφ (L.one t) = L'.one t := by
  set a := mapPt φ hφ (L.one t) with ha
  have h2 : L'.mul t a a = a := by rw [ha, ← hmul, L.one_mul]
  calc a = L'.mul t (L'.one t) a := (L'.one_mul t a).symm
    _ = L'.mul t (L'.mul t (L'.inv t a) a) a := by rw [L'.inv_mul_cancel]
    _ = L'.mul t (L'.inv t a) (L'.mul t a a) := by rw [L'.mul_assoc]
    _ = L'.mul t (L'.inv t a) a := by rw [h2]
    _ = L'.one t := L'.inv_mul_cancel t a

end DualAL

open DualAL in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (r : ℕ) [Fact r.Prime] (hrN : ¬ r ∣ N)
    {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f) (q' : E'.A ⟶ E.A) (hq' : q' ≫ E.f = E'.f)
    (h : FakeEllipticCurve.IsAtkinLehnerQuotientVia r E E' q hq q' hq') :
    FakeEllipticCurve.PreservesLevel E' E q' hq' := by
  obtain ⟨q_hom, q'_hom, q_act, q'_act, hcomp, hker, q_lev⟩ := h
  have hAL : FakeEllipticCurve.IsAtkinLehnerQuotientVia r E E' q hq q' hq' := ⟨q_hom, q'_hom, q_act, q'_act, hcomp, hker, q_lev⟩
  have hr : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ r
  haveI := E.lev_closed
  haveI := E'.lev_closed
  haveI := E.lev_finite
  haveI := E'.lev_finite
  haveI := E.lev_flat
  haveI := E'.lev_flat
  haveI := E.lev_finitePresentation
  haveI := E'.lev_finitePresentation

  obtain ⟨j, hj⟩ : FactorsThrough E'.lev (mapPt q hq (⟨E.lev, rfl⟩ : SchemeHomOver (E.lev ≫ E.f) E.f)) :=
    q_lev _ _ ⟨𝟙 _, Category.id_comp _⟩
  have hj' : j ≫ E'.lev = E.lev ≫ q := by rw [hj]; rfl

  haveI : Mono j := by
    refine ⟨fun {Z} u v huv => ?_⟩
    have hlevuv : u ≫ E.lev ≫ q = v ≫ E.lev ≫ q := by
      rw [← hj', ← Category.assoc, huv, Category.assoc]
    have ht : (v ≫ E.lev) ≫ E.f = (u ≫ E.lev) ≫ E.f := by
      rw [Category.assoc, Category.assoc, ← hq, reassoc_of% hlevuv]
    let t := (u ≫ E.lev) ≫ E.f
    let Pu : SchemeHomOver t E.f := ⟨u ≫ E.lev, rfl⟩
    let Pv : SchemeHomOver t E.f := ⟨v ≫ E.lev, ht⟩
    have hPu : FactorsThrough E.lev Pu := ⟨u, rfl⟩
    have hPv : FactorsThrough E.lev Pv := ⟨v, rfl⟩
    have hq_eq : mapPt q hq Pu = mapPt q hq Pv := by
      apply Subtype.ext; simp only [mapPt_coe, Pu, Pv, Category.assoc]; exact hlevuv

    have hD : FactorsThrough E.lev (E.L.mul t Pu (E.L.inv t Pv)) :=
      (E.lev_sub t Pu _ hPu (E.lev_sub t Pv Pv hPv hPv).2).1
    have hqD : mapPt q hq (E.L.mul t Pu (E.L.inv t Pv)) = E'.L.one t := by
      have hinv : mapPt q hq (E.L.mul t Pv (E.L.inv t Pv)) = E'.L.one t := by
        rw [E.L.mul_inv_cancel]; exact mapPt_one E.L E'.L q hq q_hom t
      rw [q_hom] at hinv ⊢
      rw [hq_eq]; exact hinv
    have hD1 := eq_one_of_factorsThrough_lev_of_mapPt_eq_one hΛℤ r hrN E E' q hq q' hq' hAL t _ hD hqD

    have hPuv : Pu = Pv := by
      have := congrArg (fun X => E.L.mul t X Pv) hD1
      rwa [E.L.mul_assoc, E.L.inv_mul_cancel, E.L.mul_one, E.L.one_mul] at this
    have := congrArg Subtype.val hPuv
    exact (cancel_mono E.lev).1 this

  have hjf : j ≫ (E'.lev ≫ E'.f) = E.lev ≫ E.f := by rw [← Category.assoc, hj', Category.assoc, hq]
  haveI : IsFinite j := by
    have : IsFinite (j ≫ (E'.lev ≫ E'.f)) := by rw [hjf]; infer_instance
    exact MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) j (E'.lev ≫ E'.f) inferInstance this
  haveI : IsClosedImmersion j := (IsClosedImmersion.iff_isFinite_and_mono j).2 ⟨inferInstance, inferInstance⟩
  haveI : IsIso j :=
    AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_eq (E.lev ≫ E.f) (E'.lev ≫ E'.f) j hjf
      (fun z => by rw [E.lev_rank, E'.lev_rank])

  intro T t P hP
  obtain ⟨P₀, hP₀⟩ := hP
  let Q : SchemeHomOver t E.f := ⟨(P₀ ≫ inv j) ≫ E.lev, by
    rw [Category.assoc, ← hjf, ← Category.assoc, Category.assoc P₀, IsIso.inv_hom_id, Category.comp_id, ← Category.assoc, hP₀,
      P.2]⟩
  have hQ : FactorsThrough E.lev Q := ⟨P₀ ≫ inv j, rfl⟩
  have hqQ : mapPt q hq Q = P := by
    apply Subtype.ext
    simp only [mapPt_coe, Q, Category.assoc]
    rw [← hj', ← Category.assoc (inv j), IsIso.inv_hom_id, Category.id_comp, hP₀]
  obtain ⟨hc1, -⟩ := hcomp hr
  have hfin : mapPt q' hq' P = pushPt (E.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩) (E.act_over _) Q := by
    apply Subtype.ext
    rw [← hqQ]
    simp only [mapPt_coe, Category.assoc]
    rw [hc1]
  rw [hfin]
  exact E.lev_stable _ t Q hQ

end S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_symm_of_isAtkinLehnerQuotientVia_of_not_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_symm_of_isAtkinLehnerQuotientVia_of_not_dvd (solution)
