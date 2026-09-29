-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.natCard_properLine_image_subset_lev
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/cbfd24ae-1128-5d67-89de-18d0fe7e8c59

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_equiv_levPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_equiv_levPoints"
namespace QM
p2m_export "CerednikDrinfeld.QM" "pushPt FactorsThrough nsmulPt FakeEllipticCurve FakeEllipticCurve.exists_equiv_levPoints"
namespace FakeEllipticCurve
p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve" "A f mk act_hom lev_stable comm act act_one L lev_one act_mul act_add lev lev_sub act_over exists_equiv_levPoints"
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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.Pts"

def TorsPts (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) :
    AddSubgroup (Pts E t) where
  carrier := {P | nsmulPt E.L t n P = E.L.one t}
  zero_mem' := by
    change n • (0 : Pts E t) = 0
    exact nsmul_zero n
  add_mem' {P Q} hP hQ := by
    change n • P = 0 at hP
    change n • Q = 0 at hQ
    change n • (P + Q) = 0
    rw [nsmul_add, hP, hQ, add_zero]
  neg_mem' {P} hP := by
    change n • P = 0 at hP
    change n • (-P) = 0
    rw [neg_nsmul, hP, neg_zero]

namespace TorsPts

variable (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ)

theorem mem_iff (P : Pts E t) : P ∈ TorsPts E t n ↔ nsmulPt E.L t n P = E.L.one t := Iff.rfl

theorem mem_iff_nsmul_eq_zero (P : Pts E t) : P ∈ TorsPts E t n ↔ n • P = 0 := Iff.rfl

def equivSubtype : ↥(TorsPts E t n) ≃ {P : SchemeHomOver t E.f // nsmulPt E.L t n P = E.L.one t} := Equiv.refl _

theorem natCard_eq :
    Nat.card ↥(TorsPts E t n) = Nat.card {P : SchemeHomOver t E.f // nsmulPt E.L t n P = E.L.one t} := rfl

theorem nsmul_eq_zero (P : ↥(TorsPts E t n)) : n • P = 0 := by
  apply Subtype.ext
  rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
  exact (mem_iff_nsmul_eq_zero E t n P.1).1 P.2

theorem actHom_mem (m : ↥Λ) {P : Pts E t} (hP : P ∈ TorsPts E t n) : Pts.actHom E t m P ∈ TorsPts E t n := by
  rw [mem_iff_nsmul_eq_zero] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

def torsAct (m : ↥Λ) : ↥(TorsPts E t n) →+ ↥(TorsPts E t n) :=
  ((Pts.actHom E t m).domRestrict (TorsPts E t n)).codRestrict (TorsPts E t n)
    (fun P => actHom_mem E t n m P.2)

@[scoped simp] theorem coe_torsAct (m : ↥Λ) (P : ↥(TorsPts E t n)) :
    ((torsAct E t n m P) : Pts E t) = Pts.actHom E t m P := rfl

theorem torsAct_apply_coe_coe (m : ↥Λ) (P : ↥(TorsPts E t n)) :
    (Pts.val E t (torsAct E t n m P)).1 = (Pts.val E t (P : Pts E t)).1 ≫ E.act m := rfl

theorem val_torsAct (m : ↥Λ) (P : ↥(TorsPts E t n)) :
    Pts.val E t (torsAct E t n m P) = pushPt (E.act m) (E.act_over m) (Pts.val E t (P : Pts E t)) := rfl

theorem torsAct_one (h : (1 : ℍ[ℚ, a, b]) ∈ Λ) : torsAct E t n ⟨1, h⟩ = AddMonoidHom.id _ := by
  ext P; apply Subtype.ext
  rw [coe_torsAct, Pts.actHom_one]; rfl

theorem torsAct_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    torsAct E t n ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (torsAct E t n x).comp (torsAct E t n y) := by
  ext P; apply Subtype.ext
  rw [coe_torsAct, Pts.actHom_mul]; rfl

theorem torsAct_add (x y : ↥Λ) : torsAct E t n (x + y) = torsAct E t n x + torsAct E t n y := by
  ext P; apply Subtype.ext
  rw [coe_torsAct, Pts.actHom_add]; rfl

theorem torsAct_natCast (hΛ : IsOrder Λ) (m : ℕ) (hm : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (P : ↥(TorsPts E t n)) :
    torsAct E t n ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩ P = m • P := by
  apply Subtype.ext
  rw [coe_torsAct, Pts.actHom_natCast E t hΛ m hm, AddSubgroup.coe_nsmul]

theorem torsAct_self_eq_zero (hΛ : IsOrder Λ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    torsAct E t n ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ = 0 := by
  ext P
  rw [torsAct_natCast E t n hΛ n hn, nsmul_eq_zero]; rfl

theorem torsAct_eq_zero_of_eq_natCast_mul (hΛ : IsOrder Λ) (m m' : ↥Λ)
    (h : (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) : torsAct E t n m = 0 := by
  have hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := Pts.natCast_mem hΛ n
  obtain ⟨mv, hmv⟩ := m
  change mv = ((n : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) at h
  subst h
  rw [torsAct_mul E t n ⟨_, hn⟩ m' hmv, torsAct_self_eq_zero E t n hΛ hn, AddMonoidHom.zero_comp]

end TorsPts
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts"

end CerednikDrinfeld.QM.FakeEllipticCurve
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld"

namespace ASM21
namespace M2L

variable {ℓ : ℕ}

def row0 (x : Fin 2 → ZMod ℓ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := Matrix.of ![x, 0]

@[scoped simp] theorem row0_apply_zero (x : Fin 2 → ZMod ℓ) : row0 x 0 = x := rfl
@[scoped simp] theorem row0_apply_one (x : Fin 2 → ZMod ℓ) : row0 x 1 = 0 := rfl

theorem row0_add (x y : Fin 2 → ZMod ℓ) : row0 (x + y) = row0 x + row0 y := by
  ext i j; fin_cases i <;> simp [row0]
theorem row0_zero : row0 (0 : Fin 2 → ZMod ℓ) = 0 := by
  ext i j; fin_cases i <;> simp [row0]
theorem row0_smul (c : ZMod ℓ) (x : Fin 2 → ZMod ℓ) : row0 (c • x) = (algebraMap (ZMod ℓ) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) c) * row0 x := by
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  ext i j; fin_cases i <;> simp [row0]
theorem row0_eq_zero_iff (x : Fin 2 → ZMod ℓ) : row0 x = 0 ↔ x = 0 := by
  constructor
  · intro h; funext j; have := congrFun (congrFun h 0) j; simpa [row0] using this
  · rintro rfl; exact row0_zero

theorem single_mul_eq_row0 (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (i : Fin 2) :
    Matrix.of (fun a b => if a = 0 ∧ b = i then (1 : ZMod ℓ) else 0) * X = row0 (X i) := by
  ext a b; fin_cases a <;> fin_cases i <;> simp [row0, Matrix.mul_apply, Fin.sum_univ_two]

theorem low_mul_row0 (y : Fin 2 → ZMod ℓ) :
    Matrix.of (fun a b => if a = 1 ∧ b = 0 then (1 : ZMod ℓ) else 0) * row0 y = Matrix.of ![0, y] := by
  ext a b; fin_cases a <;> simp [row0, Matrix.mul_apply, Fin.sum_univ_two]
theorem eq_row0_add (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) : X = row0 (X 0) + Matrix.of ![0, X 1] := by
  ext a b; fin_cases a <;> simp [row0]

def rowSp (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ) where
  carrier := {x | row0 x ∈ I}
  zero_mem' := by show row0 0 ∈ I; rw [row0_zero]; exact I.zero_mem
  add_mem' := by intro x y hx hy; show row0 (x + y) ∈ I; rw [row0_add]; exact I.add_mem hx hy
  smul_mem' := by intro c x hx; show row0 (c • x) ∈ I; rw [row0_smul]; exact I.smul_mem _ hx

theorem mem_rowSp (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) (x : Fin 2 → ZMod ℓ) : x ∈ rowSp I ↔ row0 x ∈ I := Iff.rfl

def idealOf (W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)) : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) where
  carrier := {X | ∀ i, X i ∈ W}
  zero_mem' := by
    show ∀ i, (0 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) i ∈ W
    intro i; exact W.zero_mem
  add_mem' := by
    intro X Y hX hY
    show ∀ i, (X + Y) i ∈ W
    intro i; exact W.add_mem (hX i) (hY i)
  smul_mem' := by
    intro Y X hX i
    have : (Y • X) i = ∑ k, Y i k • X k := by
      funext j; simp [Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    exact W.sum_mem (fun k _ => W.smul_mem _ (hX k))

theorem mem_idealOf (W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)) (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) : X ∈ idealOf W ↔ ∀ i, X i ∈ W := Iff.rfl

theorem rowSp_idealOf (W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)) : rowSp (idealOf W) = W := by
  ext x
  rw [mem_rowSp, mem_idealOf]
  constructor
  · intro h; simpa using h 0
  · intro h i; fin_cases i <;> simp [h]

theorem idealOf_rowSp (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) : idealOf (rowSp I) = I := by
  ext X
  rw [mem_idealOf]
  constructor
  · intro h
    have h0 : row0 (X 0) ∈ I := (mem_rowSp I _).1 (h 0)
    have h1 : row0 (X 1) ∈ I := (mem_rowSp I _).1 (h 1)
    rw [eq_row0_add X, ← low_mul_row0]
    exact I.add_mem h0 (I.smul_mem _ h1)
  · intro hX i
    rw [mem_rowSp, ← single_mul_eq_row0]
    exact I.smul_mem _ hX

def idealEquiv : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) ≃ Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ) where
  toFun := rowSp
  invFun := idealOf
  left_inv := idealOf_rowSp
  right_inv := rowSp_idealOf

theorem rowSp_bot : rowSp (⊥ : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) = ⊥ := by
  ext x; rw [mem_rowSp, Submodule.mem_bot, Submodule.mem_bot, row0_eq_zero_iff]
theorem rowSp_top : rowSp (⊤ : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) = ⊤ := by
  ext x; simp [mem_rowSp]
theorem idealOf_inf (W W' : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)) : idealOf (W ⊓ W') = idealOf W ⊓ idealOf W' := by
  ext X; simp only [mem_idealOf, Submodule.mem_inf]; exact forall_and
theorem idealOf_bot : idealOf (⊥ : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)) = ⊥ := by
  rw [← rowSp_bot, idealOf_rowSp]

def properEquiv :
    {I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) // I ≠ ⊥ ∧ I ≠ ⊤} ≃
    {W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ) // W ≠ ⊥ ∧ W ≠ ⊤} where
  toFun I := ⟨rowSp I.1, fun h => I.2.1 (by rw [← idealOf_rowSp I.1, h, ← rowSp_bot, idealOf_rowSp]),
    fun h => I.2.2 (by rw [← idealOf_rowSp I.1, h, ← rowSp_top, idealOf_rowSp])⟩
  invFun W := ⟨idealOf W.1, fun h => W.2.1 (by rw [← rowSp_idealOf W.1, h, rowSp_bot]),
    fun h => W.2.2 (by rw [← rowSp_idealOf W.1, h, rowSp_top])⟩
  left_inv I := Subtype.ext (idealOf_rowSp I.1)
  right_inv W := Subtype.ext (rowSp_idealOf W.1)

section lines
variable [Fact ℓ.Prime]

theorem finrank_two : Module.finrank (ZMod ℓ) (Fin 2 → ZMod ℓ) = 2 := by simp

theorem exists_eq_span {W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)} (h1 : W ≠ ⊥) (h2 : W ≠ ⊤) :
    ∃ (v : Fin 2 → ZMod ℓ) (hv : v ≠ 0), W = (Projectivization.mk (ZMod ℓ) v hv).submodule := by
  obtain ⟨v, hvW, hv0⟩ := (Submodule.ne_bot_iff W).1 h1
  refine ⟨v, hv0, ?_⟩
  rw [Projectivization.submodule_mk]
  have hle : Submodule.span (ZMod ℓ) {v} ≤ W := Submodule.span_le.2 (by simpa using hvW)
  have hlt : Module.finrank (ZMod ℓ) W < Module.finrank (ZMod ℓ) (Fin 2 → ZMod ℓ) :=
    Submodule.finrank_lt h2
  rw [finrank_two] at hlt
  have h1' : Module.finrank (ZMod ℓ) (Submodule.span (ZMod ℓ) {v}) = 1 := finrank_span_singleton hv0
  symm
  apply Submodule.eq_of_le_of_finrank_le hle
  omega

theorem span_ne_bot_ne_top (p : Projectivization (ZMod ℓ) (Fin 2 → ZMod ℓ)) : p.submodule ≠ ⊥ ∧ p.submodule ≠ ⊤ := by
  have h := p.finrank_submodule
  constructor
  · intro hb; rw [hb, finrank_bot] at h; exact zero_ne_one h
  · intro ht; rw [ht, finrank_top, finrank_two] at h; omega

noncomputable def linesEquiv :
    {W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ) // W ≠ ⊥ ∧ W ≠ ⊤} ≃ Projectivization (ZMod ℓ) (Fin 2 → ZMod ℓ) := by
  classical
  refine (Equiv.ofBijective (fun p : Projectivization (ZMod ℓ) (Fin 2 → ZMod ℓ) =>
    (⟨p.submodule, span_ne_bot_ne_top p⟩ : {W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ) // W ≠ ⊥ ∧ W ≠ ⊤})) ⟨?_, ?_⟩).symm
  · intro p q h; exact Projectivization.submodule_injective (congrArg Subtype.val h)
  · rintro ⟨W, hW1, hW2⟩
    obtain ⟨v, hv, rfl⟩ := exists_eq_span hW1 hW2
    exact ⟨_, rfl⟩

theorem natCard_lines : Nat.card {W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ) // W ≠ ⊥ ∧ W ≠ ⊤} = ℓ + 1 := by
  rw [Nat.card_congr linesEquiv, Projectivization.card_of_finrank_two (ZMod ℓ) (Fin 2 → ZMod ℓ) finrank_two,
    Nat.card_eq_fintype_card, ZMod.card]

theorem inf_eq_bot_of_ne {W W' : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)} (h1 : W ≠ ⊥) (h2 : W ≠ ⊤) (h1' : W' ≠ ⊥) (h2' : W' ≠ ⊤)
    (hne : W ≠ W') : W ⊓ W' = ⊥ := by
  obtain ⟨v, hv, rfl⟩ := exists_eq_span h1 h2
  obtain ⟨v', hv', rfl⟩ := exists_eq_span h1' h2'
  by_contra h
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨huv, huv'⟩ := Submodule.mem_inf.1 hu
  apply hne
  have key : ∀ (p : Projectivization (ZMod ℓ) (Fin 2 → ZMod ℓ)), u ∈ p.submodule → p.submodule = Submodule.span (ZMod ℓ) {u} := by
    intro p hup
    have hle : Submodule.span (ZMod ℓ) {u} ≤ p.submodule := Submodule.span_le.2 (by simpa using hup)
    symm
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [p.finrank_submodule, finrank_span_singleton hu0]
  rw [key _ huv, key _ huv']

end lines
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve"

end ASM21.M2L
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.ASM21 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.ASM21.M2L"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.ASM21"

namespace LOP29

abbrev Mat (ℓ : ℕ) : Type := Matrix (Fin 2) (Fin 2) (ZMod ℓ)

section Dict

variable {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hord : IsOrder Λ) (ℓ : ℕ) [Fact ℓ.Prime]
  (M : Type) [AddCommGroup M] (ρ : ↥Λ → M →+ M)
  (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
  (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
  (P₀ : M) (hgen : ∀ P : M, ∃ m : ↥Λ, P = ρ m P₀)
  (hann : ∀ m : ↥Λ, ρ m P₀ = 0 ↔ ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]))
  (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ))
  (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
  (hφsurj : Function.Surjective φ)
  (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))

theorem coe_mul_eq_ratsmul (y : ℍ[ℚ, a, b]) : ((ℓ : ℚ) : ℍ[ℚ, a, b]) * y = (ℓ : ℚ) • y :=
  QuaternionAlgebra.coe_mul_eq_smul _ _

theorem zsmul_eq_coe_mul (y : ℍ[ℚ, a, b]) : (ℓ : ℤ) • y = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * y := by
  rw [zsmul_eq_mul, Int.cast_natCast, ← QuaternionAlgebra.coe_natCast]

include hann hφker in
theorem rho_eq_zero_iff_phi (m : ↥Λ) : ρ m P₀ = 0 ↔ φ m = 0 := by
  rw [hann, hφker]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, by rw [hy, coe_mul_eq_ratsmul]⟩
  · rintro ⟨y, hy⟩; exact ⟨y, by rw [hy, coe_mul_eq_ratsmul]⟩

def ev : ↥Λ →+ M := AddMonoidHom.mk' (fun m => ρ m P₀) (fun x y => by simp [ρ_add])

include ρ_add in
theorem ev_apply (m : ↥Λ) : ev Λ M ρ ρ_add P₀ m = ρ m P₀ := rfl

include ρ_add hann hφker in
theorem rho_eq_iff_phi (m m' : ↥Λ) : ρ m P₀ = ρ m' P₀ ↔ φ m = φ m' := by
  rw [← sub_eq_zero, ← ev_apply Λ M ρ ρ_add P₀, ← ev_apply Λ M ρ ρ_add P₀, ← map_sub, ev_apply,
    rho_eq_zero_iff_phi Λ ℓ M ρ P₀ hann φ hφker, map_sub, sub_eq_zero]

include hord ρ_mul in
theorem rho_mul_apply (n m : ↥Λ) (P : M) :
    ρ ⟨(n : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]), hord.mul_mem n.2 m.2⟩ P = ρ n (ρ m P) := by
  rw [ρ_mul]; rfl

def idealImg (J : Submodule ℤ ℍ[ℚ, a, b]) (hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) :
    Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) where
  carrier := {A | ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ φ m = A}
  zero_mem' := ⟨0, J.zero_mem, map_zero φ⟩
  add_mem' := by
    rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
    exact ⟨m + m', J.add_mem hm hm', map_add φ m m'⟩
  smul_mem' := by
    rintro A _ ⟨m, hm, rfl⟩
    obtain ⟨n, rfl⟩ := hφsurj A
    exact ⟨⟨(n : ℍ[ℚ, a, b]) * m, hord.mul_mem n.2 m.2⟩, hleft _ n.2 _ hm, by rw [hφmul, smul_eq_mul]⟩

theorem mem_idealImg (J : Submodule ℤ ℍ[ℚ, a, b]) (hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) :
    A ∈ idealImg Λ hord ℓ φ hφmul hφsurj J hleft ↔ ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ φ m = A := Iff.rfl

include hφker in

theorem mem_of_phi_mem_idealImg (J : Submodule ℤ ℍ[ℚ, a, b]) (hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J)
    (hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) (m : ↥Λ)
    (hm : φ m ∈ idealImg Λ hord ℓ φ hφmul hφsurj J hleft) : (m : ℍ[ℚ, a, b]) ∈ J := by
  obtain ⟨m', hm', he⟩ := hm
  have : φ (m - m') = 0 := by rw [map_sub, he, sub_self]
  obtain ⟨y, hy⟩ := (hφker _).mp this
  have : (m : ℍ[ℚ, a, b]) = m' + (ℓ : ℤ) • (y : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_coe_mul, coe_mul_eq_ratsmul, ← hy]; simp
  rw [this]
  exact J.add_mem hm' (hℓJ _ y.2)

include ρ_add hann hφker in

theorem mem_of_rho_eq (J : Submodule ℤ ℍ[ℚ, a, b]) (hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) (m m' : ↥Λ)
    (hm' : (m' : ℍ[ℚ, a, b]) ∈ J) (h : ρ m P₀ = ρ m' P₀) : (m : ℍ[ℚ, a, b]) ∈ J := by
  have hφ : φ (m - m') = 0 := by
    rw [map_sub, sub_eq_zero]; exact (rho_eq_iff_phi Λ ℓ M ρ ρ_add P₀ hann φ hφker m m').mp h
  obtain ⟨y, hy⟩ := (hφker _).mp hφ
  have : (m : ℍ[ℚ, a, b]) = m' + (ℓ : ℤ) • (y : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_coe_mul, coe_mul_eq_ratsmul, ← hy]; simp
  rw [this]
  exact J.add_mem hm' (hℓJ _ y.2)

include hann in
theorem rho_zsmul_ell (y : ↥Λ) : ρ ((ℓ : ℤ) • y) P₀ = 0 :=
  (hann _).mpr ⟨y, by rw [Submodule.coe_smul, zsmul_eq_coe_mul]⟩

noncomputable def equivMat : M ≃ Matrix (Fin 2) (Fin 2) (ZMod ℓ) where
  toFun P := φ (Classical.choose (hgen P))
  invFun A := ρ (Classical.choose (hφsurj A)) P₀
  left_inv P := by
    have h1 := Classical.choose_spec (hgen P)
    have h2 := Classical.choose_spec (hφsurj (φ (Classical.choose (hgen P))))
    exact ((rho_eq_iff_phi Λ ℓ M ρ ρ_add P₀ hann φ hφker _ _).mpr h2).trans h1.symm
  right_inv A := by
    have h2 := Classical.choose_spec (hφsurj A)
    have h1 := Classical.choose_spec (hgen (ρ (Classical.choose (hφsurj A)) P₀))
    exact ((rho_eq_iff_phi Λ ℓ M ρ ρ_add P₀ hann φ hφker _ _).mp h1.symm).trans h2

include ρ_add hgen hann hφsurj hφker in
theorem natCard_M : Nat.card M = ℓ ^ 4 := by
  rw [Nat.card_congr (equivMat Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker), Nat.card_eq_fintype_card]
  show Fintype.card (Fin 2 → Fin 2 → ZMod ℓ) = ℓ ^ 4
  rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← pow_mul]

theorem eq_bot_or_eq_of_le_span {v : Fin 2 → ZMod ℓ} (hv : v ≠ 0) (W' : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ))
    (h : W' ≤ Submodule.span (ZMod ℓ) {v}) : W' = ⊥ ∨ W' = Submodule.span (ZMod ℓ) {v} := by
  by_cases hb : W' = ⊥
  · exact Or.inl hb
  · right
    apply le_antisymm h
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W').1 hb
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (h hw)
    have hc : c ≠ 0 := by rintro rfl; exact hw0 (zero_smul _ v)
    rw [Submodule.span_le, Set.singleton_subset_iff]
    have : v = c⁻¹ • (c • v) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [SetLike.mem_coe, this]
    exact W'.smul_mem _ hw

end Dict
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.ASM21 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.ASM21.M2L"

end LOP29
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.ASM21 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.ASM21.M2L"

namespace LOP29

section PartA

variable {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hord : IsOrder Λ) (ℓ : ℕ) [Fact ℓ.Prime]
  (M : Type) [AddCommGroup M] (ρ : ↥Λ → M →+ M)
  (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
  (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
  (P₀ : M) (hgen : ∀ P : M, ∃ m : ↥Λ, P = ρ m P₀)
  (hann : ∀ m : ↥Λ, ρ m P₀ = 0 ↔ ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]))
  (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ))
  (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
  (hφsurj : Function.Surjective φ)
  (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))

include ρ_add hgen hann hφsurj hφker in

theorem equivMat_apply_rho (m : ↥Λ) :
    equivMat Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker (ρ m P₀) = φ m := by
  have h1 := Classical.choose_spec (hgen (ρ m P₀))
  show φ (Classical.choose (hgen (ρ m P₀))) = φ m
  exact ((rho_eq_iff_phi Λ ℓ M ρ ρ_add P₀ hann φ hφker _ _).mp h1).symm

include ρ_add hgen hann hφsurj hφker in
theorem equivMat_symm_apply_phi (m : ↥Λ) :
    (equivMat Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker).symm (φ m) = ρ m P₀ := by
  rw [Equiv.symm_apply_eq, equivMat_apply_rho]

include ρ_add hgen hann hφsurj hφker in
theorem equivMat_add (P Q : M) :
    equivMat Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker (P + Q) =
      equivMat Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker P + equivMat Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker Q := by
  obtain ⟨m, rfl⟩ := hgen P
  obtain ⟨m', rfl⟩ := hgen Q
  have : ρ m P₀ + ρ m' P₀ = ρ (m + m') P₀ := by rw [ρ_add, AddMonoidHom.add_apply]
  rw [this, equivMat_apply_rho, equivMat_apply_rho, equivMat_apply_rho, map_add]

include hord ρ_mul ρ_add hgen hann hφmul hφsurj hφker in

theorem partA_equiv (J : Submodule ℤ ℍ[ℚ, a, b])
    (hJ : J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) :
    ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : M // (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀)},
      ∀ x y : ZMod ℓ × ZMod ℓ,
        ((e (x + y) : {P : M // (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀)}) : M) = (e x : M) + (e y : M) := by
  classical
  obtain ⟨hJle, hJℓ, hJmul, ⟨x₀, hx₀J, hx₀⟩, hJne⟩ := hJ

  let EM := equivMat Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker
  have hEM : ∀ m : ↥Λ, EM (ρ m P₀) = φ m := equivMat_apply_rho Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker
  have hEMs : ∀ m : ↥Λ, EM.symm (φ m) = ρ m P₀ := equivMat_symm_apply_phi Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker
  have hEMadd : ∀ P Q : M, EM (P + Q) = EM P + EM Q := equivMat_add Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker
  let I := idealImg Λ hord ℓ φ hφmul hφsurj J hJmul
  have hImem : ∀ A, A ∈ I ↔ ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ φ m = A := fun A => Iff.rfl
  let W := ASM21.M2L.rowSp I
  have hIW : ∀ X, X ∈ I ↔ ∀ i, X i ∈ W := fun X => by
    rw [← ASM21.M2L.mem_idealOf, ASM21.M2L.idealOf_rowSp]

  have hIb : I ≠ ⊥ := by
    intro h
    have hmem : φ ⟨x₀, hJle hx₀J⟩ ∈ I := ⟨⟨x₀, hJle hx₀J⟩, hx₀J, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    obtain ⟨y, hy⟩ := (hφker _).mp hmem
    exact hx₀ ⟨y, y.2, by rw [zsmul_eq_coe_mul, coe_mul_eq_ratsmul]; exact hy⟩
  have hIt : I ≠ ⊤ := by
    intro h
    apply hJne
    apply le_antisymm hJle
    intro m hm
    exact mem_of_phi_mem_idealImg Λ hord ℓ φ hφmul hφsurj hφker J hJℓ hJmul ⟨m, hm⟩
      (by rw [show idealImg Λ hord ℓ φ hφmul hφsurj J hJmul = ⊤ from h]; exact Submodule.mem_top)
  have hWb : W ≠ ⊥ := by
    intro h; apply hIb
    rw [← ASM21.M2L.idealOf_rowSp I, show ASM21.M2L.rowSp I = ⊥ from h, ASM21.M2L.idealOf_bot]
  have hWt : W ≠ ⊤ := by
    intro h; apply hIt
    rw [← ASM21.M2L.idealOf_rowSp I, show ASM21.M2L.rowSp I = ⊤ from h, ← ASM21.M2L.rowSp_top, ASM21.M2L.idealOf_rowSp]
  obtain ⟨v, hv0, hWv⟩ := ASM21.M2L.exists_eq_span hWb hWt
  rw [Projectivization.submodule_mk] at hWv

  let eW : ZMod ℓ ≃ₗ[ZMod ℓ] W :=
    (LinearEquiv.toSpanNonzeroSingleton (ZMod ℓ) (Fin 2 → ZMod ℓ) v hv0).trans (LinearEquiv.ofEq _ _ hWv.symm)

  let S := {P : M // (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀)}
  have hSmem : ∀ P : S, EM P.1 ∈ I := by
    rintro ⟨P, m, hm, rfl⟩
    rw [hEM]; exact ⟨m, hm, rfl⟩
  have hrow : ∀ (P : S) (i : Fin 2), EM P.1 i ∈ W := fun P i => (hIW _).mp (hSmem P) i
  let f : S → ZMod ℓ × ZMod ℓ := fun P => (eW.symm ⟨EM P.1 0, hrow P 0⟩, eW.symm ⟨EM P.1 1, hrow P 1⟩)

  let mk : ZMod ℓ × ZMod ℓ → Matrix (Fin 2) (Fin 2) (ZMod ℓ) := fun c i =>
    if i = 0 then ((eW c.1 : W) : Fin 2 → ZMod ℓ) else ((eW c.2 : W) : Fin 2 → ZMod ℓ)
  have hmk0 : ∀ c, mk c 0 = ((eW c.1 : W) : Fin 2 → ZMod ℓ) := fun c => by simp [mk]
  have hmk1 : ∀ c, mk c 1 = ((eW c.2 : W) : Fin 2 → ZMod ℓ) := fun c => by simp [mk]
  have hmk : ∀ c : ZMod ℓ × ZMod ℓ, mk c ∈ I := by
    intro c
    apply (hIW _).mpr
    rw [Fin.forall_fin_two, hmk0, hmk1]
    exact ⟨(eW c.1).2, (eW c.2).2⟩
  let g : ZMod ℓ × ZMod ℓ → S := fun c =>
    ⟨EM.symm (mk c), by
      obtain ⟨m, hm, hφm⟩ := (hImem _).mp (hmk c)
      exact ⟨m, hm, by rw [← hφm, hEMs]⟩⟩
  have hg : ∀ c, (g c : M) = EM.symm (mk c) := fun c => rfl
  have hgf : ∀ P : S, g (f P) = P := by
    intro P
    apply Subtype.ext
    rw [hg, Equiv.symm_apply_eq]
    funext i
    revert i
    rw [Fin.forall_fin_two, hmk0, hmk1]
    simp [f]
  have hfg : ∀ c, f (g c) = c := by
    intro c
    obtain ⟨c1, c2⟩ := c
    simp only [f]
    have h0 : (⟨EM (g (c1, c2)).1 0, hrow (g (c1, c2)) 0⟩ : W) = eW c1 := by
      apply Subtype.ext
      show EM (g (c1, c2)).1 0 = _
      rw [hg, Equiv.apply_symm_apply, hmk0]
    have h1 : (⟨EM (g (c1, c2)).1 1, hrow (g (c1, c2)) 1⟩ : W) = eW c2 := by
      apply Subtype.ext
      show EM (g (c1, c2)).1 1 = _
      rw [hg, Equiv.apply_symm_apply, hmk1]
    rw [h0, h1, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  let e : ZMod ℓ × ZMod ℓ ≃ S := ⟨g, f, hfg, hgf⟩

  have hf_add : ∀ (P Q : S) (h : (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P.1 + Q.1 = ρ m P₀)),
      f ⟨P.1 + Q.1, h⟩ = f P + f Q := by
    intro P Q h
    have hW0 : (⟨EM (P.1 + Q.1) 0, hrow ⟨P.1 + Q.1, h⟩ 0⟩ : W) = ⟨EM P.1 0, hrow P 0⟩ + ⟨EM Q.1 0, hrow Q 0⟩ :=
      Subtype.ext (by simp only [Submodule.coe_add, hEMadd]; rfl)
    have hW1 : (⟨EM (P.1 + Q.1) 1, hrow ⟨P.1 + Q.1, h⟩ 1⟩ : W) = ⟨EM P.1 1, hrow P 1⟩ + ⟨EM Q.1 1, hrow Q 1⟩ :=
      Subtype.ext (by simp only [Submodule.coe_add, hEMadd]; rfl)
    simp only [f]
    rw [hW0, hW1, map_add, map_add, Prod.mk_add_mk]
  refine ⟨e, fun x y => ?_⟩

  have hmemxy : ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ (e x : M) + (e y : M) = ρ m P₀ := by
    obtain ⟨m, hm, hme⟩ := (e x).2
    obtain ⟨m', hm', hme'⟩ := (e y).2
    exact ⟨m + m', J.add_mem hm hm', by rw [hme, hme', ρ_add, AddMonoidHom.add_apply]⟩
  have key : f (e (x + y)) = f ⟨(e x : M) + (e y : M), hmemxy⟩ := by
    rw [hf_add, show f (e (x + y)) = x + y from hfg (x + y), show f (e x) = x from hfg x, show f (e y) = y from hfg y]
  have := congrArg g key
  rw [hgf, hgf] at this
  exact congrArg Subtype.val this

end PartA
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.ASM21 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.ASM21.M2L"

end LOP29
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.ASM21 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.ASM21.M2L"

namespace C5Lev

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

section Aux

variable {k : Type} [Field k] (E : FakeEllipticCurve Λ N k)

theorem nsmulPt_eq_pow (n : ℕ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) :
    letI := E.L.pointGroup (𝟙 (Spec (CommRingCat.of k)))
    nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) n P = P ^ n := by
  letI := E.L.pointGroup (𝟙 (Spec (CommRingCat.of k)))
  induction n with
  | zero => rfl
  | succ n ih =>
    show E.L.mul _ (nsmulPt E.L _ n P) P = P ^ (n + 1)
    rw [ih, pow_succ]; rfl

theorem equiv_zero (e : ZMod N × ZMod N ≃ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough E.lev P})
    (he : ∀ x y : ZMod N × ZMod N,
      ((e (x + y) : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough E.lev P}) :
          SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) = E.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y)) :
    ((e 0 : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough E.lev P}) :
        SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) = E.L.one (𝟙 (Spec (CommRingCat.of k))) := by
  letI := E.L.pointGroup (𝟙 (Spec (CommRingCat.of k)))
  have h := he 0 0
  rw [add_zero] at h
  change (e 0).1 = (e 0).1 * (e 0).1 at h
  have : (e 0).1 * 1 = (e 0).1 * (e 0).1 := by rw [mul_one]; exact h
  exact (mul_left_cancel this).symm

theorem equiv_nsmul (e : ZMod N × ZMod N ≃ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough E.lev P})
    (he : ∀ x y : ZMod N × ZMod N,
      ((e (x + y) : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough E.lev P}) :
          SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) = E.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y))
    (n : ℕ) (c : ZMod N × ZMod N) :
    ((e (n • c) : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough E.lev P}) :
        SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) =
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) n (e c) := by
  letI := E.L.pointGroup (𝟙 (Spec (CommRingCat.of k)))
  rw [nsmulPt_eq_pow]
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact equiv_zero E e he
  | succ n ih => rw [succ_nsmul, he, ih, pow_succ]; rfl

theorem natCard_torsionBy_zmod_le (ℓ : ℕ) [Fact ℓ.Prime] [NeZero N] :
    Nat.card {x : ZMod N // ℓ • x = 0} ≤ ℓ := by
  let K : AddSubgroup (ZMod N) :=
    { carrier := {x | ℓ • x = 0}
      zero_mem' := smul_zero _
      add_mem' := fun {x y} hx hy => by show ℓ • (x + y) = 0; rw [smul_add, hx, hy, add_zero]
      neg_mem' := fun {x} hx => by show ℓ • (-x) = 0; rw [smul_neg, hx, neg_zero] }
  have hK : Nat.card {x : ZMod N // ℓ • x = 0} = Nat.card K := rfl
  rw [hK]
  haveI : IsAddCyclic K := inferInstance
  have hexp : AddMonoid.exponent K ∣ ℓ := by
    apply AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero
    rintro ⟨x, hx⟩
    exact Subtype.ext hx
  haveI : Finite K := inferInstance
  rw [← IsAddCyclic.exponent_eq_card]
  exact Nat.le_of_dvd (Fact.out : ℓ.Prime).pos hexp

theorem natCard_torsionBy_prod_le (ℓ : ℕ) [Fact ℓ.Prime] [NeZero N] :
    Nat.card {c : ZMod N × ZMod N // ℓ • c = 0} ≤ ℓ ^ 2 := by
  have e : {c : ZMod N × ZMod N // ℓ • c = 0} ≃ {x : ZMod N // ℓ • x = 0} × {x : ZMod N // ℓ • x = 0} :=
    { toFun := fun c => (⟨c.1.1, (Prod.ext_iff.mp c.2).1⟩, ⟨c.1.2, (Prod.ext_iff.mp c.2).2⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), Prod.ext_iff.mpr ⟨p.1.2, p.2.2⟩⟩
      left_inv := fun c => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, pow_two]
  exact Nat.mul_le_mul (natCard_torsionBy_zmod_le ℓ) (natCard_torsionBy_zmod_le ℓ)

end Aux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.ASM21 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.ASM21.M2L"

theorem eq_one_of_not_dvd (k : Type) [Field k] [IsAlgClosed k] [NeZero N] (hNk : (N : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) (hP : FactorsThrough E.lev P)
    (hℓP : nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) ℓ P = E.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    P = E.L.one (𝟙 (Spec (CommRingCat.of k))) := by
  obtain ⟨e, he⟩ := FakeEllipticCurve.exists_equiv_levPoints k hNk E
  obtain ⟨c, hc⟩ := e.surjective ⟨P, hP⟩
  have hPc : P = (e c).1 := by rw [hc]
  have h1 : (e (ℓ • c)).1 = (e 0).1 := by
    rw [equiv_nsmul E e he, equiv_zero E e he, ← hPc, hℓP]
  have h2 : ℓ • c = 0 := e.injective (Subtype.ext h1)
  have hunit : IsUnit (ℓ : ZMod N) := by
    rw [ZMod.isUnit_prime_iff_not_dvd (Fact.out : ℓ.Prime)]; exact hℓN
  have hc0 : c = 0 := by
    have h3 : (ℓ : ZMod N) • c = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact h2
    obtain ⟨u, hu⟩ := hunit
    have h4 : u • c = 0 := by rw [Units.smul_def, hu]; exact h3
    calc c = u⁻¹ • (u • c) := (inv_smul_smul u c).symm
      _ = 0 := by rw [h4, smul_zero]
  rw [hPc, hc0, equiv_zero E e he]

theorem exists_ne_one_of_dvd (k : Type) [Field k] [IsAlgClosed k] [NeZero N] (hNk : (N : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ℓ ∣ N) :
    ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough E.lev P ∧
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) ℓ P = E.L.one (𝟙 (Spec (CommRingCat.of k))) ∧
      P ≠ E.L.one (𝟙 (Spec (CommRingCat.of k))) := by
  obtain ⟨e, he⟩ := FakeEllipticCurve.exists_equiv_levPoints k hNk E
  obtain ⟨d, hd⟩ := hℓN
  have hN0 : N ≠ 0 := NeZero.ne N
  have hd0 : d ≠ 0 := by rintro rfl; exact hN0 (by rw [hd, mul_zero])
  have hℓ2 := (Fact.out : ℓ.Prime).two_le

  let c : ZMod N × ZMod N := ((d : ZMod N), 0)
  have hcℓ : ℓ • c = 0 := by
    refine Prod.ext ?_ ?_
    · show ℓ • ((d : ℕ) : ZMod N) = 0
      rw [nsmul_eq_mul, ← Nat.cast_mul, ← hd, ZMod.natCast_self]
    · show ℓ • (0 : ZMod N) = 0
      exact smul_zero _
  have hcne : c ≠ 0 := by
    intro h0
    have h1 : ((d : ℕ) : ZMod N) = 0 := congrArg Prod.fst h0
    rw [ZMod.natCast_eq_zero_iff] at h1
    have hle : N ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) h1
    have h2 : 2 * d ≤ ℓ * d := Nat.mul_le_mul_right d hℓ2
    rw [← hd] at h2
    omega
  refine ⟨(e c).1, (e c).2, ?_, ?_⟩
  · rw [← equiv_nsmul E e he, hcℓ, equiv_zero E e he]
  · intro h1
    apply hcne
    apply e.injective
    apply Subtype.ext
    rw [h1, equiv_zero E e he]

theorem natCard_le (k : Type) [Field k] [IsAlgClosed k] [NeZero N] (hNk : (N : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k) (ℓ : ℕ) [Fact ℓ.Prime] :
    Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f //
      FactorsThrough E.lev P ∧ nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) ℓ P = E.L.one (𝟙 (Spec (CommRingCat.of k)))} ≤ ℓ ^ 2 := by
  classical
  obtain ⟨e, he⟩ := FakeEllipticCurve.exists_equiv_levPoints k hNk E
  haveI : Finite {c : ZMod N × ZMod N // ℓ • c = 0} := inferInstance
  refine le_trans ?_ (natCard_torsionBy_prod_le (N := N) ℓ)
  apply Nat.card_le_card_of_injective
    (fun P => (⟨e.symm ⟨P.1, P.2.1⟩, by
      apply e.injective
      apply Subtype.ext
      rw [equiv_nsmul E e he, Equiv.apply_symm_apply, equiv_zero E e he]
      exact P.2.2⟩ : {c : ZMod N × ZMod N // ℓ • c = 0}))
  intro P Q h
  have h1 := congrArg Subtype.val h
  have h2 := e.symm.injective h1
  exact Subtype.ext (congrArg (fun x : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough E.lev P} => x.1) h2)

end C5Lev
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.ASM21 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.ASM21.M2L"

open _root_.CerednikDrinfeld.QM.FakeEllipticCurve _root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.CerednikDrinfeld.QM.FakeEllipticCurve in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0) (hNk : (N : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f)
    (hP₀ : nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) ℓ P₀ = E.L.one (𝟙 (Spec (CommRingCat.of k))))
    (hgen : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) ℓ P = E.L.one (𝟙 (Spec (CommRingCat.of k))) →
        ∃ m : ↥Λ, P = pushPt (E.act m) (E.act_over m) P₀)
    (hann : ∀ m : ↥Λ, pushPt (E.act m) (E.act_over m) P₀ = E.L.one (𝟙 (Spec (CommRingCat.of k))) ↔
      ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) :
    Nat.card {J : Submodule ℤ ℍ[ℚ, a, b] //
        (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) ∧
        ∀ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J → FactorsThrough E.lev (pushPt (E.act m) (E.act_over m) P₀)} =
      (if ℓ ∣ N then 1 else 0) := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder
  have hℓp : ℓ.Prime := Fact.out
  have hℓ2 : 2 ≤ ℓ := hℓp.two_le

  let M : Type := ↥(TorsPts E (𝟙 (Spec (CommRingCat.of k))) ℓ)
  let ρ : ↥Λ → M →+ M := TorsPts.torsAct E (𝟙 (Spec (CommRingCat.of k))) ℓ
  have ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y) := TorsPts.torsAct_mul E (𝟙 (Spec (CommRingCat.of k))) ℓ
  have ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y := TorsPts.torsAct_add E (𝟙 (Spec (CommRingCat.of k))) ℓ
  let ρ' : ↥Λ →+ (M →+ M) := AddMonoidHom.mk' ρ ρ_add
  have hρ0 : ρ 0 = 0 := by
    change ρ' 0 = 0
    exact map_zero ρ'
  have hρneg : ∀ m : ↥Λ, ρ (-m) = -ρ m := fun m => by
    change ρ' (-m) = -ρ' m
    exact map_neg ρ' m
  let Q₀ : M := ⟨Pts.of E (𝟙 (Spec (CommRingCat.of k))) P₀, hP₀⟩
  have hval : ∀ (m : ↥Λ), Pts.val E (𝟙 (Spec (CommRingCat.of k))) (ρ m Q₀ : M).1 =
      pushPt (E.act m) (E.act_over m) P₀ := fun m => rfl
  have hgen' : ∀ P : M, ∃ m : ↥Λ, P = ρ m Q₀ := by
    intro P
    obtain ⟨m, hm⟩ := hgen (Pts.val E (𝟙 (Spec (CommRingCat.of k))) (P : M).1) ((TorsPts.mem_iff E (𝟙 (Spec (CommRingCat.of k))) ℓ P.1).mp P.2)
    exact ⟨m, Subtype.ext hm⟩
  have hann' : ∀ m : ↥Λ, ρ m Q₀ = 0 ↔ ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) := by
    intro m
    rw [← hann m]
    constructor
    · intro h; exact congrArg (fun P : M => Pts.val E (𝟙 (Spec (CommRingCat.of k))) (P : M).1) h
    · intro h; exact Subtype.ext h
  obtain ⟨φ, -, hφmul, hφsurj, hφker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ ℓ hℓq hℓq'

  let LevT := {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f //
      FactorsThrough E.lev P ∧ nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) ℓ P = E.L.one (𝟙 (Spec (CommRingCat.of k)))}
  haveI hfinLevT : Finite LevT := by
    obtain ⟨eN, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_equiv_levPoints k hNk E
    haveI : Finite {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough E.lev P} := Finite.of_equiv _ eN
    exact Finite.of_injective
      (fun P : LevT => (⟨P.1, P.2.1⟩ : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough E.lev P}))
      (fun P Q h => Subtype.ext (by simpa using congrArg Subtype.val h))
  have hLevT : Nat.card LevT ≤ ℓ ^ 2 := C5Lev.natCard_le k hNk E ℓ

  have hSJ : ∀ (J : Submodule ℤ ℍ[ℚ, a, b]),
      (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
        (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) →
      Finite {P : M // ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m Q₀} ∧
      Nat.card {P : M // ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m Q₀} = ℓ ^ 2 := by
    intro J hJ
    obtain ⟨e, -⟩ := LOP29.partA_equiv Λ hO ℓ M ρ ρ_mul ρ_add Q₀ hgen' hann' φ hφmul hφsurj hφker J hJ
    refine ⟨Finite.of_equiv _ e, ?_⟩
    rw [← Nat.card_congr e, Nat.card_prod, Nat.card_zmod, pow_two]

  have hinj : ∀ (J : Submodule ℤ ℍ[ℚ, a, b])
      (hlev : ∀ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J → FactorsThrough E.lev (pushPt (E.act m) (E.act_over m) P₀)),
      ∃ ι : {P : M // ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m Q₀} → LevT, Function.Injective ι ∧
        ∀ P, (ι P).1 = Pts.val E (𝟙 (Spec (CommRingCat.of k))) (P.1 : M).1 := by
    intro J hlev
    refine ⟨fun P => ⟨Pts.val E (𝟙 (Spec (CommRingCat.of k))) (P.1 : M).1, ?_, (TorsPts.mem_iff E (𝟙 (Spec (CommRingCat.of k))) ℓ P.1.1).mp P.1.2⟩, ?_, fun P => rfl⟩
    · obtain ⟨m, hm, hPm⟩ := P.2
      rw [hPm, hval]; exact hlev m hm
    · intro P Q h
      have h' := congrArg Subtype.val h
      apply Subtype.ext; apply Subtype.ext
      exact h'
  by_cases hℓN : ℓ ∣ N
  · rw [if_pos hℓN]

    let J₀ : AddSubgroup ℍ[ℚ, a, b] :=
      { carrier := {x | ∃ hx : x ∈ Λ, FactorsThrough E.lev (Pts.val E (𝟙 (Spec (CommRingCat.of k))) (ρ ⟨x, hx⟩ Q₀ : M).1)}
        zero_mem' := ⟨Λ.zero_mem, by
          have h0 : (ρ ⟨0, Λ.zero_mem⟩ Q₀ : M) = 0 := by
            rw [show (⟨0, Λ.zero_mem⟩ : ↥Λ) = 0 from rfl, hρ0, AddMonoidHom.zero_apply]
          rw [h0]
          exact E.lev_one _⟩
        add_mem' := by
          rintro x y ⟨hx, hxP⟩ ⟨hy, hyP⟩
          refine ⟨Λ.add_mem hx hy, ?_⟩
          have : (ρ ⟨x + y, Λ.add_mem hx hy⟩ Q₀ : M) = ρ ⟨x, hx⟩ Q₀ + ρ ⟨y, hy⟩ Q₀ := by
            rw [show (⟨x + y, Λ.add_mem hx hy⟩ : ↥Λ) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, ρ_add, AddMonoidHom.add_apply]
          rw [this]
          exact (E.lev_sub _ _ _ hxP hyP).1
        neg_mem' := by
          rintro x ⟨hx, hxP⟩
          refine ⟨Λ.neg_mem hx, ?_⟩
          have : (ρ ⟨-x, Λ.neg_mem hx⟩ Q₀ : M) = -ρ ⟨x, hx⟩ Q₀ := by
            rw [show (⟨-x, Λ.neg_mem hx⟩ : ↥Λ) = -⟨x, hx⟩ from rfl, hρneg, AddMonoidHom.neg_apply]
          rw [this]
          exact (E.lev_sub _ _ _ hxP hxP).2 }
    let J : Submodule ℤ ℍ[ℚ, a, b] := AddSubgroup.toIntSubmodule J₀
    have hJmem : ∀ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ↔
        FactorsThrough E.lev (Pts.val E (𝟙 (Spec (CommRingCat.of k))) (ρ m Q₀ : M).1) := by
      intro m
      change (∃ hx : (m : ℍ[ℚ, a, b]) ∈ Λ, _) ↔ _
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨m.2, h⟩⟩
    have hJle : J ≤ Λ := fun x hx => by
      obtain ⟨hxΛ, -⟩ := (show x ∈ J₀ from hx); exact hxΛ
    have hJℓ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J := by
      intro y hy
      apply (hJmem ⟨(ℓ : ℤ) • y, Λ.smul_mem _ hy⟩).mpr
      have : (ρ ⟨(ℓ : ℤ) • y, Λ.smul_mem _ hy⟩ Q₀ : M) = 0 := by
        rw [show (⟨(ℓ : ℤ) • y, Λ.smul_mem _ hy⟩ : ↥Λ) = (ℓ : ℤ) • ⟨y, hy⟩ from rfl]
        exact LOP29.rho_zsmul_ell Λ ℓ M ρ Q₀ hann' ⟨y, hy⟩
      rw [this]
      exact E.lev_one _
    have hJmul : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J := by
      intro m hm x hx
      have hxΛ := hJle hx
      have hxP := (hJmem ⟨x, hxΛ⟩).mp hx
      apply (hJmem ⟨m * x, hO.mul_mem hm hxΛ⟩).mpr
      rw [LOP29.rho_mul_apply Λ hO M ρ ρ_mul ⟨m, hm⟩ ⟨x, hxΛ⟩ Q₀]
      exact E.lev_stable ⟨m, hm⟩ _ _ hxP
    have hlevJ : ∀ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J → FactorsThrough E.lev (pushPt (E.act m) (E.act_over m) P₀) :=
      fun m hm => by rw [← hval]; exact (hJmem m).mp hm

    have hJwit : ∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y := by
      obtain ⟨P, hPlev, hPtors, hPne⟩ := C5Lev.exists_ne_one_of_dvd k hNk E ℓ hℓN
      let PM : M := ⟨Pts.of E (𝟙 (Spec (CommRingCat.of k))) P, hPtors⟩
      obtain ⟨m, hm⟩ := hgen' PM
      refine ⟨m, (hJmem m).mpr (by rw [← hm]; exact hPlev), ?_⟩
      rintro ⟨y, hy, hmy⟩
      apply hPne
      have h0 : ρ m Q₀ = 0 := (hann' m).mpr ⟨⟨y, hy⟩, by rw [hmy, LOP29.zsmul_eq_coe_mul ℓ y]⟩
      have : PM = 0 := by rw [hm, h0]
      exact congrArg (fun R : M => Pts.val E (𝟙 (Spec (CommRingCat.of k))) (R : M).1) this
    have hJne : J ≠ Λ := by
      intro hJΛ

      have hall : ∀ P : M, FactorsThrough E.lev (Pts.val E (𝟙 (Spec (CommRingCat.of k))) (P : M).1) := by
        intro P
        obtain ⟨m, rfl⟩ := hgen' P
        exact (hJmem m).mp (by rw [hJΛ]; exact m.2)
      let ι : M → LevT := fun P => ⟨Pts.val E (𝟙 (Spec (CommRingCat.of k))) (P : M).1, hall P, (TorsPts.mem_iff E (𝟙 (Spec (CommRingCat.of k))) ℓ P.1).mp P.2⟩
      have hι : Function.Injective ι := fun P Q h => by
        have h' := congrArg Subtype.val h
        exact Subtype.ext h'
      have h1 : Nat.card M ≤ Nat.card LevT := Nat.card_le_card_of_injective ι hι
      have h2 : Nat.card M = ℓ ^ 4 := LOP29.natCard_M Λ ℓ M ρ ρ_add Q₀ hgen' hann' φ hφsurj hφker
      have h3 : ℓ ^ 4 ≤ ℓ ^ 2 := by rw [← h2]; exact h1.trans hLevT
      have h4 : ℓ ^ 2 < ℓ ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
    have hJall : (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
        (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) := ⟨hJle, hJℓ, hJmul, hJwit, hJne⟩

    have hsub : ∀ (J₁ J₂ : Submodule ℤ ℍ[ℚ, a, b]),
        (J₁ ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J₁) ∧ (∀ m ∈ Λ, ∀ x ∈ J₁, m * x ∈ J₁) ∧
          (∃ x ∈ J₁, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J₁ ≠ Λ) →
        (∀ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J₁ → FactorsThrough E.lev (pushPt (E.act m) (E.act_over m) P₀)) →
        (J₂ ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J₂) ∧ (∀ m ∈ Λ, ∀ x ∈ J₂, m * x ∈ J₂) ∧
          (∃ x ∈ J₂, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J₂ ≠ Λ) →
        (∀ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J₂ → FactorsThrough E.lev (pushPt (E.act m) (E.act_over m) P₀)) →
        J₁ ≤ J₂ := by
      intro J₁ J₂ hJ₁ hlev₁ hJ₂ hlev₂ x hx
      have hxΛ : x ∈ Λ := hJ₁.1 hx
      obtain ⟨hfin₂, hcard₂⟩ := hSJ J₂ hJ₂
      obtain ⟨ι₂, hι₂, hι₂val⟩ := hinj J₂ hlev₂
      haveI := hfin₂
      have hbij : Function.Bijective ι₂ := hι₂.bijective_of_nat_card_le (by rw [hcard₂]; exact hLevT)

      have hxT : FactorsThrough E.lev (Pts.val E (𝟙 (Spec (CommRingCat.of k))) (ρ ⟨x, hxΛ⟩ Q₀ : M).1) := by
        rw [hval]; exact hlev₁ ⟨x, hxΛ⟩ hx
      obtain ⟨P', hP'⟩ := hbij.2 ⟨Pts.val E (𝟙 (Spec (CommRingCat.of k))) (ρ ⟨x, hxΛ⟩ Q₀ : M).1, hxT, (TorsPts.mem_iff E (𝟙 (Spec (CommRingCat.of k))) ℓ (ρ ⟨x, hxΛ⟩ Q₀ : M).1).mp (ρ ⟨x, hxΛ⟩ Q₀).2⟩
      obtain ⟨m', hm', hPm'⟩ := P'.2
      have heq : ρ ⟨x, hxΛ⟩ Q₀ = ρ m' Q₀ := by
        have := congrArg Subtype.val hP'
        rw [hι₂val] at this
        rw [← hPm']
        exact (Subtype.ext this).symm
      exact LOP29.mem_of_rho_eq Λ ℓ M ρ ρ_add Q₀ hann' φ hφker J₂ hJ₂.2.1 ⟨x, hxΛ⟩ m' hm' heq
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨⟨fun J₁ J₂ => Subtype.ext (le_antisymm (hsub J₁.1 J₂.1 J₁.2.1 J₁.2.2 J₂.2.1 J₂.2.2)
      (hsub J₂.1 J₁.1 J₂.2.1 J₂.2.2 J₁.2.1 J₁.2.2))⟩, ⟨⟨J, hJall, hlevJ⟩⟩⟩
  · rw [if_neg hℓN]
    haveI : IsEmpty {J : Submodule ℤ ℍ[ℚ, a, b] //
        (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) ∧
        ∀ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J → FactorsThrough E.lev (pushPt (E.act m) (E.act_over m) P₀)} := by
      refine ⟨fun J => ?_⟩
      obtain ⟨hfin, hcard⟩ := hSJ J.1 J.2.1
      haveI := hfin

      have hsub : Subsingleton {P : M // ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J.1 ∧ P = ρ m Q₀} := by
        refine ⟨fun P Q => ?_⟩
        have hzero : ∀ R : {P : M // ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J.1 ∧ P = ρ m Q₀}, (R.1 : M) = 0 := by
          intro R
          obtain ⟨m, hm, hRm⟩ := R.2
          have hlev : FactorsThrough E.lev (Pts.val E (𝟙 (Spec (CommRingCat.of k))) (R.1 : M).1) := by
            rw [hRm, hval]; exact J.2.2 m hm
          have := C5Lev.eq_one_of_not_dvd k hNk E ℓ hℓN _ hlev ((TorsPts.mem_iff E (𝟙 (Spec (CommRingCat.of k))) ℓ R.1.1).mp R.1.2)
          exact Subtype.ext this
        exact Subtype.ext ((hzero P).trans (hzero Q).symm)
      have h1 : Nat.card {P : M // ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J.1 ∧ P = ρ m Q₀} ≤ 1 :=
        Finite.card_le_one_iff_subsingleton.mpr hsub
      rw [hcard] at h1
      have : 2 ^ 2 ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ2 2
      omega
    exact Nat.card_of_isEmpty

end S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev (solution)
