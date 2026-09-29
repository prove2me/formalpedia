-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_transfer_forall_factorsThrough_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/eac9f860-da93-5350-8c7b-9f7d7db6fbac

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM"
open scoped Quaternion
open QuaternionAlgebra

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.ExtraLevel QM.FakeEllipticCurve"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.ExtraLevel mapPt mapPt_coe pushPt FactorsThrough nsmulPt geomPoint FakeEllipticCurve"
namespace FakeEllipticCurve
p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve" "ExtraLevel A f act_hom comm act act_one L lev_one act_mul act_add lev lev_sub act_over bundle pushPt_act_natCast_eq_nsmulPt"
p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve CerednikDrinfeld.QM CerednikDrinfeld"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

def Pts (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) : Type u :=
  SchemeHomOver t E.f

namespace Pts

variable (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))

def of (P : SchemeHomOver t E.f) : Pts E t := P

def val (P : Pts E t) : SchemeHomOver t E.f := P

@[scoped simp] theorem val_of (P : SchemeHomOver t E.f) : val E t (of E t P) = P := rfl
@[scoped simp] theorem of_val (P : Pts E t) : of E t (val E t P) = P := rfl

def equiv : SchemeHomOver t E.f ≃ Pts E t := Equiv.refl _

scoped instance instZero : Zero (Pts E t) := ⟨E.L.one t⟩
scoped instance instAdd : Add (Pts E t) := ⟨fun P Q => E.L.mul t P Q⟩
scoped instance instNeg : Neg (Pts E t) := ⟨fun P => E.L.inv t P⟩

scoped instance instAddCommGroup : AddCommGroup (Pts E t) where
  add_assoc := E.L.mul_assoc t
  zero_add := E.L.one_mul t
  add_zero := E.L.mul_one t
  nsmul n P := nsmulPt E.L t n P
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  neg_add_cancel := E.L.inv_mul_cancel t
  add_comm := E.comm t
  zsmul := zsmulRec (fun n P => nsmulPt E.L t n P)

theorem add_def (P Q : Pts E t) : P + Q = E.L.mul t P Q := rfl
theorem zero_def : (0 : Pts E t) = E.L.one t := rfl
theorem neg_def (P : Pts E t) : -P = E.L.inv t P := rfl

theorem nsmul_eq_nsmulPt (n : ℕ) (P : Pts E t) : n • P = nsmulPt E.L t n P := rfl

def actHom (m : ↥Λ) : Pts E t →+ Pts E t where
  toFun P := pushPt (E.act m) (E.act_over m) P
  map_zero' := by
    show pushPt (E.act m) (E.act_over m) (E.L.one t) = E.L.one t
    have h := E.act_hom m t (E.L.one t) (E.L.one t)
    rw [E.L.one_mul] at h

    have := congrArg (E.L.mul t (E.L.inv t (pushPt (E.act m) (E.act_over m) (E.L.one t)))) h
    rw [← E.L.mul_assoc, E.L.inv_mul_cancel, E.L.one_mul] at this
    exact this.symm
  map_add' P Q := E.act_hom m t P Q

theorem actHom_apply (m : ↥Λ) (P : Pts E t) : actHom E t m P = pushPt (E.act m) (E.act_over m) P := rfl

theorem coe_actHom_apply (m : ↥Λ) (P : Pts E t) :
    (val E t (actHom E t m P)).1 = (val E t P).1 ≫ E.act m := rfl

theorem actHom_one (h : (1 : ℍ[ℚ, a, b]) ∈ Λ) : actHom E t ⟨1, h⟩ = AddMonoidHom.id _ := by
  ext P
  apply Subtype.ext
  show (val E t P).1 ≫ E.act ⟨1, h⟩ = (val E t P).1
  rw [E.act_one h, Category.comp_id]

theorem actHom_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    actHom E t ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (actHom E t x).comp (actHom E t y) := by
  ext P
  apply Subtype.ext
  show (val E t P).1 ≫ E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ((val E t P).1 ≫ E.act y) ≫ E.act x
  rw [E.act_mul x y h, Category.assoc]

theorem actHom_add (x y : ↥Λ) : actHom E t (x + y) = actHom E t x + actHom E t y := by
  ext P
  exact E.act_add x y t P

theorem actHom_mul' (x y : ℍ[ℚ, a, b]) (hx : x ∈ Λ) (hy : y ∈ Λ) (h : x * y ∈ Λ) :
    actHom E t ⟨x * y, h⟩ = (actHom E t ⟨x, hx⟩).comp (actHom E t ⟨y, hy⟩) :=
  actHom_mul E t ⟨x, hx⟩ ⟨y, hy⟩ h

theorem actHom_zero : actHom E t (0 : ↥Λ) = 0 := by
  have h2 := actHom_add E t (0 : ↥Λ) 0
  rw [add_zero] at h2
  have := congrArg (fun f => f - actHom E t (0 : ↥Λ)) h2
  simp only [sub_self, add_sub_cancel_right] at this
  exact this.symm

theorem actHom_nsmul (k : ℕ) (m : ↥Λ) (P : Pts E t) : actHom E t (k • m) P = k • actHom E t m P := by
  induction k with
  | zero => rw [zero_smul, zero_smul, actHom_zero]; rfl
  | succ k ih => rw [succ_nsmul, succ_nsmul, actHom_add, AddMonoidHom.add_apply, ih]

theorem natCast_mem (hΛ : IsOrder Λ) (n : ℕ) : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]; norm_cast
  rw [this]; exact Λ.smul_mem _ hΛ.one_mem

theorem actHom_natCast (hΛ : IsOrder Λ) (n : ℕ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (P : Pts E t) :
    actHom E t ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ P = n • P := by
  induction n with
  | zero =>
    have e : (⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hn⟩ : ↥Λ) = 0 := by apply Subtype.ext; simp
    rw [e, zero_smul, actHom_zero]; rfl
  | succ n ih =>
    have hn' : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := natCast_mem hΛ n
    have e : (⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hn⟩ : ↥Λ) = ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn'⟩ + ⟨1, hΛ.one_mem⟩ := by
      apply Subtype.ext; push_cast; rfl
    rw [e, actHom_add, AddMonoidHom.add_apply, ih hn', actHom_one, AddMonoidHom.id_apply, succ_nsmul]

end Pts
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM.FakeEllipticCurve.Pts"

end CerednikDrinfeld.QM.FakeEllipticCurve
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM.FakeEllipticCurve"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld"

namespace TwoPrimeSwitch

p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM.FakeEllipticCurve"

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

theorem map_inv_of_hom {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    mapPt φ hφ (L.inv t P) = L'.inv t (mapPt φ hφ P) := by
  have h1 : L'.mul t (mapPt φ hφ (L.inv t P)) (mapPt φ hφ P) = L'.one t := by
    rw [← hhom, L.inv_mul_cancel, map_one_of_hom L L' φ hφ hhom t]
  have := congrArg (fun Q => L'.mul t Q (L'.inv t (mapPt φ hφ P))) h1
  rw [L'.mul_assoc, L'.mul_inv_cancel, L'.mul_one, L'.one_mul] at this
  exact this

section Transfer

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

theorem eq_one_of_nsmulPt_coprime (X : FakeEllipticCurve Λ N S) {ℓ ℓ' : ℕ} (hcop : ℓ.Coprime ℓ')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t X.f)
    (h1 : nsmulPt X.L t ℓ P = X.L.one t) (h2 : nsmulPt X.L t ℓ' P = X.L.one t) : P = X.L.one t := by

  change (Pts.of X t P : Pts X t) = 0
  have e1 : (ℓ : ℤ) • (Pts.of X t P) = 0 := by rw [natCast_zsmul]; exact h1
  have e2 : (ℓ' : ℤ) • (Pts.of X t P) = 0 := by rw [natCast_zsmul]; exact h2
  have hg : ((ℓ : ℤ) * Nat.gcdA ℓ ℓ' + (ℓ' : ℤ) * Nat.gcdB ℓ ℓ') = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]; rfl
  calc (Pts.of X t P : Pts X t) = (1 : ℤ) • Pts.of X t P := (one_zsmul _).symm
    _ = ((ℓ : ℤ) * Nat.gcdA ℓ ℓ' + (ℓ' : ℤ) * Nat.gcdB ℓ ℓ') • Pts.of X t P := by rw [hg]
    _ = 0 := by rw [add_smul, mul_comm, mul_smul, e1, smul_zero, mul_comm, mul_smul, e2, smul_zero, add_zero]

theorem nsmulPt_mem_levK (X : FakeEllipticCurve Λ N S) {m : ℕ} (K' : X.ExtraLevel m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t X.f)
    (hP : FactorsThrough K'.levK P) : FactorsThrough K'.levK (nsmulPt X.L t n P) := by
  induction n with
  | zero => exact K'.levK_one t
  | succ n ih => exact (K'.levK_sub t _ _ ih hP).1

theorem zsmul_mem_levK (X : FakeEllipticCurve Λ N S) {m : ℕ} (K' : X.ExtraLevel m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℤ) (P : SchemeHomOver t X.f)
    (hP : FactorsThrough K'.levK P) : FactorsThrough K'.levK (Pts.val X t (n • (Pts.of X t P))) := by
  induction n using Int.induction_on with
  | zero => rw [zero_smul]; exact K'.levK_one t
  | succ n ih =>
    rw [add_smul, one_smul]; exact (K'.levK_sub t _ _ ih hP).1
  | pred n ih =>
    rw [sub_smul, one_smul, sub_eq_add_neg]; exact (K'.levK_sub t _ _ ih (K'.levK_sub t _ _ hP hP).2).1

theorem nsmulPt_mem_lev (X : FakeEllipticCurve Λ N S)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t X.f)
    (hP : FactorsThrough X.lev P) : FactorsThrough X.lev (nsmulPt X.L t n P) := by
  induction n with
  | zero => exact X.lev_one t
  | succ n ih => exact (X.lev_sub t _ _ ih hP).1

theorem transfer (ℓ ℓ' : ℕ) [Fact ℓ'.Prime] (hcop : ℓ.Coprime ℓ')
    (X Y : FakeEllipticCurve Λ N S) (g : X.A ⟶ Y.A) (hg : g ≫ Y.f = X.f)
    (hgmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t X.f),
      mapPt g hg (X.L.mul t P Q) = Y.L.mul t (mapPt g hg P) (mapPt g hg Q))
    (hgact : ∀ x : ↥Λ, X.act x ≫ g = g ≫ Y.act x)
    (hkerℓ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t X.f),
      mapPt g hg P = Y.L.one t → nsmulPt X.L t ℓ P = X.L.one t)
    (hlevback : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t X.f),
      FactorsThrough Y.lev (mapPt g hg P) → FactorsThrough X.lev (nsmulPt X.L t ℓ P))
    (K' : X.ExtraLevel ℓ') :
    ∃ K₁' : Y.ExtraLevel ℓ',
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t Y.f),
        FactorsThrough K₁'.levK x ↔ ∃ y : SchemeHomOver t X.f, FactorsThrough K'.levK y ∧ mapPt g hg y = x := by

  have hchar : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t Y.f),
      FactorsThrough (K'.levK ≫ g) x ↔ ∃ y : SchemeHomOver t X.f, FactorsThrough K'.levK y ∧ mapPt g hg y = x := by
    intro T t x
    constructor
    · rintro ⟨P₀, hP₀⟩
      refine ⟨⟨P₀ ≫ K'.levK, ?_⟩, ⟨P₀, rfl⟩, Subtype.ext (by simpa [mapPt_coe, Category.assoc] using hP₀)⟩
      rw [Category.assoc, ← hg, ← Category.assoc (K'.levK), ← Category.assoc, hP₀]; exact x.2
    · rintro ⟨y, ⟨P₀, hP₀⟩, hy⟩
      refine ⟨P₀, ?_⟩
      rw [← hy, mapPt_coe, ← hP₀, Category.assoc]

  have hinj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (y y' : SchemeHomOver t X.f),
      FactorsThrough K'.levK y → FactorsThrough K'.levK y' → mapPt g hg y = mapPt g hg y' → y = y' := by
    intro T t y y' hy hy' h

    have hz : FactorsThrough K'.levK (X.L.mul t y (X.L.inv t y')) :=
      (K'.levK_sub t _ _ hy (K'.levK_sub t _ _ hy' hy').2).1
    have hgz : mapPt g hg (X.L.mul t y (X.L.inv t y')) = Y.L.one t := by
      rw [hgmul, map_inv_of_hom X.L Y.L g hg hgmul, h, Y.L.mul_inv_cancel]
    have h1 := hkerℓ t _ hgz
    have h2 := K'.levK_torsion t _ hz
    have hz1 := eq_one_of_nsmulPt_coprime X hcop t _ h1 h2
    have := congrArg (fun Q => X.L.mul t Q y') hz1
    rwa [X.L.mul_assoc, X.L.inv_mul_cancel, X.L.mul_one, X.L.one_mul] at this

  haveI : IsSeparated Y.f := Y.bundle.proper.toIsSeparated
  have hcomp : (K'.levK ≫ g) ≫ Y.f = K'.levK ≫ X.f := by rw [Category.assoc, hg]
  have hfin : IsFinite (K'.levK ≫ g) := by
    have : IsFinite ((K'.levK ≫ g) ≫ Y.f) := by rw [hcomp]; exact K'.levK_finite
    exact IsFinite.of_comp (K'.levK ≫ g) Y.f
  haveI : IsClosedImmersion K'.levK := K'.levK_closed
  have hmono : Mono (K'.levK ≫ g) := by
    refine ⟨fun {T} g₁ g₂ h12 => ?_⟩

    let t : T ⟶ Spec (CommRingCat.of S) := g₁ ≫ K'.levK ≫ X.f
    have ht₂ : (g₂ ≫ K'.levK) ≫ X.f = t := by
      show (g₂ ≫ K'.levK) ≫ X.f = g₁ ≫ K'.levK ≫ X.f
      rw [← hg, Category.assoc, ← Category.assoc K'.levK g, ← Category.assoc g₂, ← h12]
      simp only [Category.assoc]
    let y₁ : SchemeHomOver t X.f := ⟨g₁ ≫ K'.levK, by simp only [t, Category.assoc]⟩
    let y₂ : SchemeHomOver t X.f := ⟨g₂ ≫ K'.levK, ht₂⟩
    have hy : y₁ = y₂ := hinj t y₁ y₂ ⟨g₁, rfl⟩ ⟨g₂, rfl⟩
      (Subtype.ext (by simp only [mapPt_coe, y₁, y₂, Category.assoc]; simpa only [Category.assoc] using h12))
    have := congrArg Subtype.val hy
    exact (cancel_mono K'.levK).mp this
  refine ⟨{ K := K'.K
            levK := K'.levK ≫ g
            levK_closed := (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨hfin, hmono⟩
            levK_sub := ?_
            levK_one := ?_
            levK_torsion := ?_
            levK_stable := ?_
            levK_disjoint := ?_
            levK_finite := by rw [hcomp]; exact K'.levK_finite
            levK_flat := by rw [hcomp]; exact K'.levK_flat
            levK_finitePresentation := by rw [hcomp]; exact K'.levK_finitePresentation
            levK_rank := fun s => by rw [hcomp]; exact K'.levK_rank s
            levK_fibre := ?_ }, fun t x => hchar t x⟩
  ·
    intro T t P Q hP hQ
    obtain ⟨y, hy, rfl⟩ := (hchar t P).mp hP
    obtain ⟨y', hy', rfl⟩ := (hchar t Q).mp hQ
    refine ⟨(hchar t _).mpr ⟨X.L.mul t y y', (K'.levK_sub t _ _ hy hy').1, hgmul t y y'⟩,
      (hchar t _).mpr ⟨X.L.inv t y, (K'.levK_sub t _ _ hy hy).2, map_inv_of_hom X.L Y.L g hg hgmul t y⟩⟩
  ·
    intro T t
    exact (hchar t _).mpr ⟨X.L.one t, K'.levK_one t, map_one_of_hom X.L Y.L g hg hgmul t⟩
  ·
    intro T t P hP
    obtain ⟨y, hy, rfl⟩ := (hchar t P).mp hP
    rw [← map_nsmulPt_of_hom X.L Y.L g hg hgmul, K'.levK_torsion t y hy, map_one_of_hom X.L Y.L g hg hgmul]
  ·
    intro x T t P hP
    obtain ⟨y, hy, rfl⟩ := (hchar t P).mp hP
    refine (hchar t _).mpr ⟨pushPt (X.act x) (X.act_over x) y, K'.levK_stable x t y hy, ?_⟩
    exact Subtype.ext (by simp only [mapPt_coe, pushPt, Category.assoc, hgact])
  ·
    intro T t P hP hC
    obtain ⟨y, hy, rfl⟩ := (hchar t P).mp hP
    have hℓy : FactorsThrough X.lev (nsmulPt X.L t ℓ y) := hlevback t y hC
    have hℓy' : FactorsThrough K'.levK (nsmulPt X.L t ℓ y) := nsmulPt_mem_levK X K' t ℓ y hy
    have h1 : nsmulPt X.L t ℓ y = X.L.one t := K'.levK_disjoint t _ hℓy' hℓy
    have h2 : nsmulPt X.L t ℓ' y = X.L.one t := K'.levK_torsion t y hy
    rw [eq_one_of_nsmulPt_coprime X hcop t y h1 h2]
    exact map_one_of_hom X.L Y.L g hg hgmul t
  ·
    intro k _ _ sk hk
    obtain ⟨e₀, he₀⟩ := K'.levK_fibre k sk hk
    let F : {P : SchemeHomOver (geomPoint k sk) X.f // FactorsThrough K'.levK P} →
        {P : SchemeHomOver (geomPoint k sk) Y.f // FactorsThrough (K'.levK ≫ g) P} :=
      fun P => ⟨mapPt g hg P.1, (hchar _ _).mpr ⟨P.1, P.2, rfl⟩⟩
    have hF : Function.Bijective F := by
      constructor
      · intro P Q h
        exact Subtype.ext (hinj _ P.1 Q.1 P.2 Q.2 (congrArg Subtype.val h))
      · intro P₁
        obtain ⟨y, hy, hy1⟩ := (hchar _ P₁.1).mp P₁.2
        exact ⟨⟨y, hy⟩, Subtype.ext hy1⟩
    refine ⟨e₀.trans (Equiv.ofBijective F hF), fun x y => ?_⟩
    show mapPt g hg (e₀ (x + y)).1 = Y.L.mul _ (mapPt g hg (e₀ x).1) (mapPt g hg (e₀ y).1)
    rw [he₀, hgmul]

end Transfer
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM.FakeEllipticCurve"

end TwoPrimeSwitch
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM.FakeEllipticCurve"

open TwoPrimeSwitch _root_.CerednikDrinfeld.QM.FakeEllipticCurve _root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.CerednikDrinfeld.QM.FakeEllipticCurve in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (ℓ ℓ' : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] (hℓℓ' : ℓ ≠ ℓ')
    (E E₁ : FakeEllipticCurve Λ N S) (K : E.ExtraLevel ℓ)
    (φ : E.A ⟶ E₁.A) (hφ : φ ≫ E₁.f = E.f) (ψ : E₁.A ⟶ E.A) (hψ : ψ ≫ E.f = E₁.f)
    (hφmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E₁.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hψmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E₁.f),
      mapPt ψ hψ (E₁.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hφact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E₁.act x) (hψact : ∀ x : ↥Λ, E₁.act x ≫ ψ = ψ ≫ E.act x)
    (hφψ : ∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = E₁.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩)
    (hone : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (hker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt φ hφ P = E₁.L.one t ↔ FactorsThrough K.levK P)
    (hlev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E₁.lev (mapPt φ hφ P))
    (hlev' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t E₁.f),
      FactorsThrough E₁.lev x → ∃ P : SchemeHomOver t E.f, FactorsThrough E.lev P ∧ mapPt φ hφ P = x) :

    (∀ K' : E.ExtraLevel ℓ', ∃ K₁' : E₁.ExtraLevel ℓ',
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t E₁.f),
        FactorsThrough K₁'.levK x ↔ ∃ y : SchemeHomOver t E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) ∧

    (∀ K₁' : E₁.ExtraLevel ℓ', ∃ K' : E.ExtraLevel ℓ',
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E₁.f,
        FactorsThrough K₁'.levK x ↔ ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) ∧

    (∀ K' K'' : E.ExtraLevel ℓ',
      (∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f, FactorsThrough K'.levK y ↔ FactorsThrough K''.levK y) ↔
      (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E₁.f,
          (∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) ↔
          (∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f, FactorsThrough K''.levK y ∧ mapPt φ hφ y = x))) := by
  classical
  have hℓp : ℓ.Prime := Fact.out
  have hℓ'p : ℓ'.Prime := Fact.out
  have hcop : ℓ.Coprime ℓ' := (Nat.coprime_primes hℓp hℓ'p).mpr hℓℓ'
  have hℓΛ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have : ((ℓ : ℚ) : ℍ[ℚ, a, b]) = (ℓ : ℤ) • (1 : ℍ[ℚ, a, b]) := by rw [zsmul_eq_mul, mul_one]; norm_cast
    rw [this]; exact Λ.smul_mem _ hone
  obtain ⟨hφψ₁, hψφ₁⟩ := hφψ hℓΛ

  have hψφ_pt : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t ℓ P := by
    intro T t P
    rw [← pushPt_act_natCast_eq_nsmulPt E hone ℓ hℓΛ t P]
    exact Subtype.ext (by simp only [mapPt_coe, pushPt, Category.assoc, ← hφψ₁])
  have hφψ_pt : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E₁.f),
      mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt E₁.L t ℓ Q := by
    intro T t Q
    rw [← pushPt_act_natCast_eq_nsmulPt E₁ hone ℓ hℓΛ t Q]
    exact Subtype.ext (by simp only [mapPt_coe, pushPt, Category.assoc, ← hψφ₁])

  have hkerφ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt φ hφ P = E₁.L.one t → nsmulPt E.L t ℓ P = E.L.one t :=
    fun t P h => K.levK_torsion t P ((hker t P).mp h)
  have hlevbackφ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E₁.lev (mapPt φ hφ P) → FactorsThrough E.lev (nsmulPt E.L t ℓ P) := by
    intro T t P hP
    obtain ⟨c, hc, hcP⟩ := hlev' t _ hP
    rw [← hψφ_pt, ← hcP, hψφ_pt]
    exact nsmulPt_mem_lev E t ℓ c hc

  have hkerψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E₁.f),
      mapPt ψ hψ Q = E.L.one t → nsmulPt E₁.L t ℓ Q = E₁.L.one t := by
    intro T t Q h
    rw [← hφψ_pt, h, map_one_of_hom E.L E₁.L φ hφ hφmul]
  have hlevbackψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E₁.f),
      FactorsThrough E.lev (mapPt ψ hψ Q) → FactorsThrough E₁.lev (nsmulPt E₁.L t ℓ Q) := by
    intro T t Q hQ
    rw [← hφψ_pt]
    exact hlev t _ hQ
  have hA := fun K' : E.ExtraLevel ℓ' =>
    transfer ℓ ℓ' hcop E E₁ φ hφ hφmul hφact hkerφ hlevbackφ K'
  refine ⟨hA, ?_, ?_⟩
  ·
    intro K₁'
    obtain ⟨K', hK'⟩ := transfer ℓ ℓ' hcop E₁ E ψ hψ hψmul hψact hkerψ hlevbackψ K₁'
    refine ⟨K', fun x => ?_⟩
    constructor
    · intro hx

      have hg : ((ℓ : ℤ) * Nat.gcdA ℓ ℓ' + (ℓ' : ℤ) * Nat.gcdB ℓ ℓ') = 1 := by
        rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]; rfl
      let x₀ : Pts E₁ (𝟙 (Spec (CommRingCat.of S))) := (Nat.gcdA ℓ ℓ' : ℤ) • (Pts.of E₁ _ x)
      have hx₀ : FactorsThrough K₁'.levK (Pts.val E₁ _ x₀) := zsmul_mem_levK E₁ K₁' _ _ x hx
      have hℓ'x : (ℓ' : ℤ) • (Pts.of E₁ (𝟙 (Spec (CommRingCat.of S))) x) = 0 := by
        rw [natCast_zsmul]; exact K₁'.levK_torsion _ x hx
      have hxe : x = nsmulPt E₁.L _ ℓ (Pts.val E₁ _ x₀) := by
        change (Pts.of E₁ _ x : Pts E₁ _) = ℓ • x₀
        rw [← natCast_zsmul, smul_smul]
        calc (Pts.of E₁ _ x : Pts E₁ _) = (1 : ℤ) • Pts.of E₁ _ x := (one_zsmul _).symm
          _ = ((ℓ : ℤ) * Nat.gcdA ℓ ℓ' + (ℓ' : ℤ) * Nat.gcdB ℓ ℓ') • Pts.of E₁ _ x := by rw [hg]
          _ = ((ℓ : ℤ) * Nat.gcdA ℓ ℓ') • Pts.of E₁ _ x := by
            rw [add_smul, mul_comm (ℓ' : ℤ) _, mul_smul (Nat.gcdB ℓ ℓ' : ℤ) (ℓ' : ℤ), hℓ'x, smul_zero, add_zero]
      refine ⟨mapPt ψ hψ (Pts.val E₁ _ x₀), (hK' _ _).mpr ⟨_, hx₀, rfl⟩, ?_⟩
      rw [hφψ_pt, ← hxe]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x₁, hx₁, rfl⟩ := (hK' _ y).mp hy
      rw [hφψ_pt]
      exact nsmulPt_mem_levK E₁ K₁' _ ℓ x₁ hx₁
  ·
    intro K' K''
    constructor
    · intro h x
      exact ⟨fun ⟨y, hy, e⟩ => ⟨y, (h y).mp hy, e⟩, fun ⟨y, hy, e⟩ => ⟨y, (h y).mpr hy, e⟩⟩
    · intro h

      have key : ∀ (K₁ K₂ : E.ExtraLevel ℓ') (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f),
          (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E₁.f,
            (∃ w : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f, FactorsThrough K₁.levK w ∧ mapPt φ hφ w = x) →
            (∃ w : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f, FactorsThrough K₂.levK w ∧ mapPt φ hφ w = x)) →
          FactorsThrough K₁.levK y → FactorsThrough K₂.levK y := by
        intro K₁ K₂ y himg hy
        obtain ⟨w, hw, hwy⟩ := himg (mapPt φ hφ y) ⟨y, hy, rfl⟩

        have hz : mapPt φ hφ (E.L.mul _ y (E.L.inv _ w)) = E₁.L.one _ := by
          rw [hφmul, map_inv_of_hom E.L E₁.L φ hφ hφmul, hwy, E₁.L.mul_inv_cancel]
        have h1 : nsmulPt E.L _ ℓ (E.L.mul _ y (E.L.inv _ w)) = E.L.one _ := hkerφ _ _ hz
        have h2 : nsmulPt E.L _ ℓ' (E.L.mul _ y (E.L.inv _ w)) = E.L.one _ := by
          change ℓ' • ((Pts.of E _ y : Pts E (𝟙 (Spec (CommRingCat.of S)))) - Pts.of E _ w) = 0
          rw [smul_sub]
          have ey : ℓ' • (Pts.of E (𝟙 (Spec (CommRingCat.of S))) y) = 0 := K₁.levK_torsion _ y hy
          have ew : ℓ' • (Pts.of E (𝟙 (Spec (CommRingCat.of S))) w) = 0 := K₂.levK_torsion _ w hw
          rw [ey, ew, sub_zero]
        have hz1 := eq_one_of_nsmulPt_coprime E hcop _ _ h1 h2
        have : y = w := by
          have := congrArg (fun Q => E.L.mul _ Q w) hz1
          rwa [E.L.mul_assoc, E.L.inv_mul_cancel, E.L.mul_one, E.L.one_mul] at this
        rw [this]; exact hw
      intro y
      exact ⟨key K' K'' y (fun x => (h x).mp), key K'' K' y (fun x => (h x).mpr)⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff (solution)
