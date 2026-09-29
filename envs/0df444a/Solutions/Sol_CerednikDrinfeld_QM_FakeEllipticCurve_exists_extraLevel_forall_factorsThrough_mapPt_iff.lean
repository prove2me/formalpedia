-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_mapPt_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c41456e7-a137-5d59-82fb-e1a74e34de40

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_mapPt_iff

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra
open scoped Quaternion

namespace GLUEaux

variable {R : Type u} [CommRing R]

theorem eq_one_of_mul_self {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f) (h : L.mul t y y = y) :
    y = L.one t := by
  have := congrArg (L.mul t (L.inv t y)) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this
  exact this

theorem map_one_of_hom {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    mapPt φ hφ (L.one t) = L'.one t := by
  apply eq_one_of_mul_self
  rw [← hhom, L.one_mul]

theorem map_nsmulPt_of_hom {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact map_one_of_hom L L' φ hφ hhom t
  | succ n ih => simp only [nsmulPt]; rw [hhom, ih]

theorem mapPt_mapPt {A A' A'' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt ψ hψ (mapPt φ hφ P) = mapPt (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) P := by
  apply Subtype.ext; simp [mapPt, Category.assoc]

theorem mapPt_congr {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {φ φ' : A ⟶ A'} (h : φ = φ') (hφ : φ ≫ f' = f) (hφ' : φ' ≫ f' = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt φ hφ P = mapPt φ' hφ' P := by
  subst h; rfl

theorem mapPt_injective_of_isIso {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) [IsIso φ]
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {P Q : SchemeHomOver t f} (h : mapPt φ hφ P = mapPt φ hφ Q) :
    P = Q := by
  apply Subtype.ext
  have := congrArg Subtype.val h
  simp only [mapPt] at this
  exact (cancel_mono φ).1 this

end GLUEaux

namespace GLUEact

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

theorem natCast_mem (hΛ : IsOrder Λ) (n : ℕ) : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]; norm_cast
  rw [this]; exact Λ.smul_mem _ hΛ.one_mem

theorem act_zero_apply (E : FakeEllipticCurve Λ N S) (h0 : (0 : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨0, h0⟩) (E.act_over _) P = E.L.one t := by
  apply GLUEaux.eq_one_of_mul_self
  have := E.act_add ⟨0, h0⟩ ⟨0, h0⟩ t P
  have e : (⟨0, h0⟩ + ⟨0, h0⟩ : ↥Λ) = ⟨0, h0⟩ := by apply Subtype.ext; simp
  rw [e] at this
  exact this.symm

theorem act_natCast_apply (E : FakeEllipticCurve Λ N S) (hΛ : IsOrder Λ) (n : ℕ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩) (E.act_over _) P = nsmulPt E.L t n P := by
  induction n with
  | zero =>
    have e : (⟨((0 : ℕ) : ℚ), natCast_mem hΛ 0⟩ : ↥Λ) = ⟨0, by simpa using natCast_mem hΛ 0⟩ := by
      apply Subtype.ext; simp
    rw [show pushPt (E.act ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ 0⟩) (E.act_over _) P =
        pushPt (E.act ⟨0, by simpa using natCast_mem hΛ 0⟩) (E.act_over _) P from by
          simp only [pushPt]; exact GLUEaux.mapPt_congr (by rw [e]) _ _ P]
    exact act_zero_apply E _ t P
  | succ n ih =>
    have e : (⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩ : ↥Λ) =
        ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩ := by
      apply Subtype.ext; push_cast; rfl
    rw [show pushPt (E.act ⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩) (E.act_over _) P =
        pushPt (E.act (⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩)) (E.act_over _) P from by
          simp only [pushPt]; exact GLUEaux.mapPt_congr (by rw [e]) _ _ P]
    rw [E.act_add, ih]
    simp only [nsmulPt]
    congr 1
    simp only [pushPt]
    rw [GLUEaux.mapPt_congr (E.act_one hΛ.one_mem) _ (by simp) P]
    apply Subtype.ext; simp [mapPt]

end GLUEact

namespace GLUEgrp

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

theorem inv_inv (x : SchemeHomOver t f) : L.inv t (L.inv t x) = x := by
  calc L.inv t (L.inv t x) = L.mul t (L.inv t (L.inv t x)) (L.one t) := (L.mul_one t _).symm
    _ = L.mul t (L.inv t (L.inv t x)) (L.mul t (L.inv t x) x) := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.mul t (L.inv t (L.inv t x)) (L.inv t x)) x := by rw [L.mul_assoc]
    _ = x := by rw [L.inv_mul_cancel, L.one_mul]

theorem mul_inv_cancel (x : SchemeHomOver t f) : L.mul t x (L.inv t x) = L.one t := by
  have := L.inv_mul_cancel t (L.inv t x)
  rwa [inv_inv] at this

theorem eq_of_mul_inv_eq_one {x y : SchemeHomOver t f} (h : L.mul t x (L.inv t y) = L.one t) : x = y := by
  have := congrArg (fun z => L.mul t z y) h
  rw [L.mul_assoc, L.inv_mul_cancel, L.mul_one, L.one_mul] at this
  exact this

theorem nsmulPt_add (n m : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (n + m) P = L.mul t (nsmulPt L t n P) (nsmulPt L t m P) := by
  induction m with
  | zero => simp [nsmulPt, L.mul_one]
  | succ m ih => rw [Nat.add_succ]; simp only [nsmulPt]; rw [ih, L.mul_assoc]

theorem nsmulPt_one_pt (n : ℕ) : nsmulPt L t n (L.one t) = L.one t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [nsmulPt]; rw [ih, L.one_mul]

theorem nsmulPt_mul (n m : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (n * m) P = nsmulPt L t n (nsmulPt L t m P) := by
  induction n with
  | zero => simp [nsmulPt]
  | succ n ih => rw [Nat.succ_mul, nsmulPt_add, ih]; simp only [nsmulPt]

theorem nsmulPt_mod_eq_one {n m : ℕ} (P : SchemeHomOver t f)
    (hn : nsmulPt L t n P = L.one t) (hm : nsmulPt L t m P = L.one t) : nsmulPt L t (n % m) P = L.one t := by
  have e : n = n / m * m + n % m := (Nat.div_add_mod' n m).symm
  have := hn
  rw [e, nsmulPt_add, nsmulPt_mul, hm, nsmulPt_one_pt, L.one_mul] at this
  exact this

theorem eq_one_of_nsmulPt_eq_one_of_coprime {r N : ℕ} (hc : Nat.Coprime r N) (P : SchemeHomOver t f)
    (hr : nsmulPt L t r P = L.one t) (hN : nsmulPt L t N P = L.one t) : P = L.one t := by
  have key : ∀ a b : ℕ, nsmulPt L t a P = L.one t → nsmulPt L t b P = L.one t → nsmulPt L t (Nat.gcd a b) P = L.one t := by
    intro a b
    refine Nat.gcd.induction a b (fun n _ hn => by simpa using hn) (fun m n _ ih hm hn => ?_)
    rw [Nat.gcd_rec]
    exact ih (nsmulPt_mod_eq_one L t P hn hm) hm
  have := key r N hr hN
  rw [hc] at this
  simpa [nsmulPt, L.one_mul] using this

end GLUEgrp

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (ℓ : ℕ)
    (E' E : FakeEllipticCurve Λ N S) (e : E'.A ≅ E.A) (he : e.hom ≫ E.f = E'.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f),
      mapPt e.hom he (E'.L.mul t P Q) = E.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (hact : ∀ x : ↥Λ, E'.act x ≫ e.hom = e.hom ≫ E.act x)
    (hlev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E'.f),
      FactorsThrough E'.lev P ↔ FactorsThrough E.lev (mapPt e.hom he P))
    (K' : E'.ExtraLevel ℓ) :
    ∃ K : E.ExtraLevel ℓ,
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E'.f),
        FactorsThrough K.levK (mapPt e.hom he P) ↔ FactorsThrough K'.levK P := by
  classical

  have heinv : e.inv ≫ E'.f = E.f := by rw [← he, Iso.inv_hom_id_assoc]
  have e_inv_e : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E.f),
      mapPt e.hom he (mapPt e.inv heinv Q) = Q := by
    intro T t Q; apply Subtype.ext; simp [mapPt]
  have e_e_inv : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E'.f),
      mapPt e.inv heinv (mapPt e.hom he P) = P := by
    intro T t P; apply Subtype.ext; simp [mapPt]
  have e_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)), mapPt e.hom he (E'.L.one t) = E.L.one t :=
    fun t => GLUEaux.map_one_of_hom E'.L E.L e.hom he hmul t
  have einv_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q R : SchemeHomOver t E.f),
      mapPt e.inv heinv (E.L.mul t Q R) = E'.L.mul t (mapPt e.inv heinv Q) (mapPt e.inv heinv R) := by
    intro T t Q R
    apply GLUEaux.mapPt_injective_of_isIso e.hom he
    rw [hmul, e_inv_e, e_inv_e, e_inv_e]

  have hpts : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E.f),
      FactorsThrough (K'.levK ≫ e.hom) Q ↔ FactorsThrough K'.levK (mapPt e.inv heinv Q) := by
    intro T t Q
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, by show c ≫ K'.levK = Q.1 ≫ e.inv; rw [← hc, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, by show c ≫ K'.levK ≫ e.hom = Q.1; rw [← Category.assoc, hc]; simp [mapPt]⟩
  have hpts' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E'.f),
      FactorsThrough (K'.levK ≫ e.hom) (mapPt e.hom he P) ↔ FactorsThrough K'.levK P := by
    intro T t P; rw [hpts, e_e_inv]
  have hcomp : (K'.levK ≫ e.hom) ≫ E.f = K'.levK ≫ E'.f := by rw [Category.assoc, he]
  haveI := K'.levK_closed
  refine ⟨
    { K := K'.K
      levK := K'.levK ≫ e.hom
      levK_closed := inferInstance
      levK_sub := ?_
      levK_one := fun t => (hpts t _).2 (by rw [← e_one, e_e_inv]; exact K'.levK_one t)
      levK_torsion := ?_
      levK_stable := ?_
      levK_disjoint := ?_
      levK_finite := by rw [hcomp]; exact K'.levK_finite
      levK_flat := by rw [hcomp]; exact K'.levK_flat
      levK_finitePresentation := by rw [hcomp]; exact K'.levK_finitePresentation
      levK_rank := by intro s; rw [hcomp]; exact K'.levK_rank s
      levK_fibre := ?_ }, fun t P => hpts' t P⟩
  ·
    intro T t Q R hQ hR
    rw [hpts] at hQ hR ⊢
    constructor
    · rw [einv_hom]; exact (K'.levK_sub t _ _ hQ hR).1
    · rw [hpts]
      have : mapPt e.inv heinv (E.L.inv t Q) = E'.L.inv t (mapPt e.inv heinv Q) := by
        letI := E'.L.pointGroup t
        have h := einv_hom t (E.L.inv t Q) Q
        rw [E.L.inv_mul_cancel, GLUEaux.map_one_of_hom E.L E'.L e.inv heinv einv_hom] at h
        exact (inv_eq_of_mul_eq_one_left h.symm).symm
      rw [this]; exact (K'.levK_sub t _ _ hQ hQ).2
  ·
    intro T t Q hQ
    rw [hpts] at hQ
    have h := K'.levK_torsion t _ hQ
    rw [← GLUEaux.map_nsmulPt_of_hom E.L E'.L e.inv heinv einv_hom] at h
    have := congrArg (mapPt e.hom he) h
    rwa [e_inv_e, e_one] at this
  ·
    intro x T t Q hQ
    rw [hpts] at hQ ⊢
    have : mapPt e.inv heinv (pushPt (E.act x) (E.act_over x) Q) = pushPt (E'.act x) (E'.act_over x) (mapPt e.inv heinv Q) := by
      simp only [pushPt]
      rw [GLUEaux.mapPt_mapPt, GLUEaux.mapPt_mapPt]
      apply GLUEaux.mapPt_congr
      rw [← cancel_epi e.hom, ← Category.assoc, ← Category.assoc, ← hact x, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      simp
    rw [this]; exact K'.levK_stable x t _ hQ
  ·
    intro T t Q hQ hC
    rw [hpts] at hQ
    have hC' : FactorsThrough E'.lev (mapPt e.inv heinv Q) := by rw [hlev, e_inv_e]; exact hC
    have := K'.levK_disjoint t _ hQ hC'
    rw [← e_inv_e t Q, this, e_one]
  ·
    intro k _ _ sk hℓ
    obtain ⟨e₀, he₀⟩ := K'.levK_fibre k sk hℓ
    refine ⟨e₀.trans ⟨fun P => ⟨mapPt e.hom he P.1, (hpts' _ P.1).2 P.2⟩,
      fun Q => ⟨mapPt e.inv heinv Q.1, (hpts _ Q.1).1 Q.2⟩,
      fun P => by apply Subtype.ext; exact e_e_inv _ P.1,
      fun Q => by apply Subtype.ext; exact e_inv_e _ Q.1⟩, ?_⟩
    intro x y
    show mapPt e.hom he (e₀ (x + y)).1 = E.L.mul _ (mapPt e.hom he (e₀ x).1) (mapPt e.hom he (e₀ y).1)
    rw [he₀, hmul]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_mapPt_iff
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_mapPt_iff (solution)
