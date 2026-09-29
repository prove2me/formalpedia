-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/60f36a5f-052b-592d-8e03-95700dc87b9c

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generalLinearGroup_forall_exists_centralizer_isFormalCompletionAlong_and_apply_eq_zpow_smul_conj
import Theorems.Thm_QuaternionAlgebra_IsOrder_star_mem_and_exists_int_trd_nrd
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective.CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective.CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective.CerednikDrinfeld.QM.FakeEllipticCurve"

open scoped Quaternion MatrixGroups

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_generalLinearGroup_forall_exists_centralizer_isFormalCompletionAlong_and_apply_eq_zpow_smul_conj QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt"
namespace QM
p2m_export "CerednikDrinfeld.QM" "mapPt pushPt nsmulPt FakeEllipticCurve FakeEllipticCurve.PreservesLevel IsOrderCoord FakeEllipticCurve.exists_generalLinearGroup_forall_exists_centralizer_isFormalCompletionAlong_and_apply_eq_zpow_smul_conj FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt"
namespace FakeEllipticCurve
p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve" "A f lev_stable act act_one L lev_one act_mul act_add lev lev_sub act_over PreservesLevel IsFormalModuleVia exists_generalLinearGroup_forall_exists_centralizer_isFormalCompletionAlong_and_apply_eq_zpow_smul_conj pushPt_act_natCast_eq_nsmulPt"
namespace EndIsoExport
p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve CerednikDrinfeld.QM CerednikDrinfeld"

section Conj

variable {a₁ b₁ : ℚ}

def cj (u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] ℍ[ℚ, a₁, b₁] where
  toFun z := ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * z * ((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])
  map_one' := by simp
  map_mul' x y := by
    calc ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (x * y) * (u : ℍ[ℚ, a₁, b₁])
        = (u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) * x * (((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
            ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) * y * (u : ℍ[ℚ, a₁, b₁]) := by
          rw [Units.mul_inv]; simp [mul_assoc]
      _ = (u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) * x * (u : ℍ[ℚ, a₁, b₁]) *
            (((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * y * (u : ℍ[ℚ, a₁, b₁])) := by
          simp [mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]
  commutes' c := by
    show ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * algebraMap ℚ ℍ[ℚ, a₁, b₁] c * (u : ℍ[ℚ, a₁, b₁]) =
      algebraMap ℚ ℍ[ℚ, a₁, b₁] c
    rw [mul_assoc, Algebra.commutes, ← mul_assoc, Units.inv_mul, one_mul]

theorem cj_apply (u : (ℍ[ℚ, a₁, b₁])ˣ) (z : ℍ[ℚ, a₁, b₁]) :
    cj u z = ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * z * ((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) := rfl

theorem uncj (u : (ℍ[ℚ, a₁, b₁])ˣ) (z : ℍ[ℚ, a₁, b₁]) :
    ((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * cj u z * ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = z := by
  rw [cj_apply]
  calc (u : ℍ[ℚ, a₁, b₁]) * ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) * z * (u : ℍ[ℚ, a₁, b₁])) * (u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)
      = ((u : ℍ[ℚ, a₁, b₁]) * (u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) * z *
          ((u : ℍ[ℚ, a₁, b₁]) * ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) := by simp [mul_assoc]
    _ = z := by rw [Units.mul_inv, one_mul, mul_one]

theorem cj_injective (u : (ℍ[ℚ, a₁, b₁])ˣ) : Function.Injective (cj u) := by
  intro x y h
  rw [← uncj u x, ← uncj u y, h]

theorem cj_units (u γ : (ℍ[ℚ, a₁, b₁])ˣ) :
    ((u⁻¹ * γ * u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = cj u (γ : ℍ[ℚ, a₁, b₁]) := by
  rw [cj_apply, Units.val_mul, Units.val_mul]

theorem cj_ratCast (u : (ℍ[ℚ, a₁, b₁])ˣ) (c : ℚ) : cj u (c : ℍ[ℚ, a₁, b₁]) = (c : ℍ[ℚ, a₁, b₁]) :=
  (cj u).commutes c

theorem cj_intCast (u : (ℍ[ℚ, a₁, b₁])ˣ) (m : ℤ) :
    cj u ((m : ℚ) : ℍ[ℚ, a₁, b₁]) = ((m : ℚ) : ℍ[ℚ, a₁, b₁]) :=
  cj_ratCast u m

end Conj

section Points

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}

theorem pushPt_congr {φ ψ : A ⟶ A} (h : φ = ψ) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B)} (P : SchemeHomOver t f) :
    pushPt φ hφ P = pushPt ψ hψ P := by
  subst h; rfl

theorem mapPt_congr {φ ψ : A ⟶ A} (h : φ = ψ) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B)} (P : SchemeHomOver t f) :
    mapPt φ hφ P = mapPt ψ hψ P := by
  subst h; rfl

theorem pushPt_id (h : 𝟙 A ≫ f = f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B)}
    (P : SchemeHomOver t f) : pushPt (𝟙 A) h P = P :=
  Subtype.ext (Category.comp_id _)

theorem pushPt_comp (φ ψ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f) (hφψ : (φ ≫ ψ) ≫ f = f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B)} (P : SchemeHomOver t f) :
    pushPt (φ ≫ ψ) hφψ P = pushPt ψ hψ (pushPt φ hφ P) :=
  Subtype.ext (Category.assoc _ _ _).symm

def tautPt (f : A ⟶ Spec (CommRingCat.of B)) : SchemeHomOver f f := ⟨𝟙 A, Category.id_comp f⟩

theorem hom_eq_of_pushPt_tautPt_eq (φ ψ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f)
    (h : pushPt φ hφ (tautPt f) = pushPt ψ hψ (tautPt f)) : φ = ψ := by
  have := congrArg Subtype.val h
  simpa [mapPt, tautPt] using this

variable (L : RelativeGroupLaw B f) {M : Type} [AddGroup M] (F : M → (A ⟶ A)) (hF : ∀ x, F x ≫ f = f)
  (hadd : ∀ (x y : M) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t f),
     pushPt (F (x + y)) (hF (x + y)) P = L.mul t (pushPt (F x) (hF x) P) (pushPt (F y) (hF y) P))
include hadd

theorem pushPt_map_zero {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t f) :
    pushPt (F 0) (hF 0) P = L.one t := by
  have h := hadd 0 0 t P
  rw [add_zero] at h
  letI := L.pointGroup t
  exact mul_eq_left.mp h.symm

theorem pushPt_map_neg {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t f) (x : M) :
    pushPt (F (-x)) (hF (-x)) P = L.inv t (pushPt (F x) (hF x) P) := by
  have h := hadd x (-x) t P
  rw [add_neg_cancel] at h
  rw [pushPt_map_zero L F hF hadd t P] at h
  letI := L.pointGroup t
  exact eq_inv_of_mul_eq_one_right h.symm

end Points

section Frame

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {B : Type} [CommRing B]
  {A₀ : FakeEllipticCurve Λ N B} {a₁ b₁ : ℚ} {R : Submodule ℤ ℍ[ℚ, a₁, b₁]}
  {ε : ↥R → (A₀.A ⟶ A₀.A)} {hε : ∀ x : ↥R, ε x ≫ A₀.f = A₀.f}

theorem intCast_mem (hR : IsOrder R) (m : ℤ) : (((m : ℚ) : ℍ[ℚ, a₁, b₁])) ∈ R := by
  have h := R.smul_mem m hR.one_mem
  rwa [Int.smul_one_eq_cast, ← coe_intCast] at h

theorem natCast_mem (hR : IsOrder R) (n : ℕ) : (((n : ℚ) : ℍ[ℚ, a₁, b₁])) ∈ R := by
  have := intCast_mem hR n
  simpa using this

theorem one_mem_Λ (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1

theorem pushPt_eps_natCast (hR : IsOrder R)
    (hε_one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R, ε ⟨1, h⟩ = 𝟙 A₀.A)
    (hε_add : ∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (ε (x + y)) (hε (x + y)) P = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    (n : ℕ) (h : (((n : ℚ) : ℍ[ℚ, a₁, b₁])) ∈ R)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f) :
    pushPt (ε ⟨((n : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩) (hε _) P = nsmulPt A₀.L t n P := by
  induction n with
  | zero =>
    have e0 : (⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ : ↥R) = 0 := Subtype.ext (by simp)
    rw [pushPt_congr (congrArg ε e0) (hε _) (hε 0) P, pushPt_map_zero A₀.L ε hε hε_add t P]
    rfl
  | succ n ih =>
    have hn : (((n : ℚ) : ℍ[ℚ, a₁, b₁])) ∈ R := natCast_mem hR n
    have es : (⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ : ↥R) = ⟨((n : ℚ) : ℍ[ℚ, a₁, b₁]), hn⟩ + ⟨1, hR.one_mem⟩ :=
      Subtype.ext (by simp)
    rw [pushPt_congr (congrArg ε es) (hε _) (hε _) P, hε_add, ih hn, pushPt_congr (hε_one hR.one_mem) (hε _)
      (Category.id_comp _) P, pushPt_id]
    rfl

theorem eps_intCast (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (hR : IsOrder R)
    (hε_one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R, ε ⟨1, h⟩ = 𝟙 A₀.A)
    (hε_add : ∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (ε (x + y)) (hε (x + y)) P = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    (m : ℤ) (h : (((m : ℚ) : ℍ[ℚ, a₁, b₁])) ∈ R) :
    ε ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℚ) : ℍ[ℚ, a, b]), hΛℤ m⟩ := by
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := one_mem_Λ hΛℤ
  refine hom_eq_of_pushPt_tautPt_eq (f := A₀.f) _ _ (hε _) (A₀.act_over _) ?_
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have hn : (((n : ℚ) : ℍ[ℚ, a₁, b₁])) ∈ R := natCast_mem hR n
    have hnΛ : (((n : ℚ) : ℍ[ℚ, a, b])) ∈ Λ := by simpa using hΛℤ n
    have e1 : (⟨((((n : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ : ↥R) = ⟨((n : ℚ) : ℍ[ℚ, a₁, b₁]), hn⟩ :=
      Subtype.ext (by simp)
    have e2 : (⟨((((n : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]), hΛℤ n⟩ : ↥Λ) = ⟨((n : ℚ) : ℍ[ℚ, a, b]), hnΛ⟩ :=
      Subtype.ext (by simp)
    rw [pushPt_congr (congrArg ε e1) (hε _) (hε _), pushPt_congr (congrArg A₀.act e2) (A₀.act_over _) (A₀.act_over _),
      pushPt_eps_natCast hR hε_one hε_add n hn,
      pushPt_act_natCast_eq_nsmulPt A₀ h1Λ n hnΛ]
  · have hn : (((n : ℚ) : ℍ[ℚ, a₁, b₁])) ∈ R := natCast_mem hR n
    have hnΛ : (((n : ℚ) : ℍ[ℚ, a, b])) ∈ Λ := by simpa using hΛℤ n
    have e1 : (⟨(((-(n : ℤ) : ℤ) : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ : ↥R) = -⟨((n : ℚ) : ℍ[ℚ, a₁, b₁]), hn⟩ :=
      Subtype.ext (by simp)
    have e2 : (⟨(((-(n : ℤ) : ℤ) : ℚ) : ℍ[ℚ, a, b]), hΛℤ _⟩ : ↥Λ) = -⟨((n : ℚ) : ℍ[ℚ, a, b]), hnΛ⟩ :=
      Subtype.ext (by simp)
    rw [pushPt_congr (congrArg ε e1) (hε _) (hε _), pushPt_congr (congrArg A₀.act e2) (A₀.act_over _) (A₀.act_over _),
      pushPt_map_neg A₀.L ε hε hε_add, pushPt_map_neg A₀.L A₀.act A₀.act_over A₀.act_add,
      pushPt_eps_natCast hR hε_one hε_add n hn,
      pushPt_act_natCast_eq_nsmulPt A₀ h1Λ n hnΛ]

def LevOK (A₀ : FakeEllipticCurve Λ N B) (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (ε : ↥R → (A₀.A ⟶ A₀.A))
    (hε : ∀ x : ↥R, ε x ≫ A₀.f = A₀.f) (w : ℍ[ℚ, a₁, b₁]) : Prop := ∃ h : w ∈ R, PreservesLevel A₀ A₀ (ε ⟨w, h⟩) (hε _)

theorem LevOK.mem {w : ℍ[ℚ, a₁, b₁]} (hw : LevOK A₀ R ε hε w) : w ∈ R := hw.elim fun h _ => h

theorem LevOK.lev {w : ℍ[ℚ, a₁, b₁]} (hw : LevOK A₀ R ε hε w) (h : w ∈ R) :
    PreservesLevel A₀ A₀ (ε ⟨w, h⟩) (hε _) := hw.elim fun _ hp => hp

theorem levOK_congr {w w' : ℍ[ℚ, a₁, b₁]} (e : w = w') (hw : LevOK A₀ R ε hε w) : LevOK A₀ R ε hε w' := e ▸ hw

theorem levOK_zero
    (hε_add : ∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (ε (x + y)) (hε (x + y)) P = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P)) :
    LevOK A₀ R ε hε 0 := by
  refine ⟨R.zero_mem, fun t P _ => ?_⟩
  have h0 : pushPt (ε 0) (hε 0) P = A₀.L.one t := pushPt_map_zero A₀.L ε hε hε_add t P
  have : mapPt (ε ⟨0, R.zero_mem⟩) (hε _) P = A₀.L.one t := h0
  rw [this]
  exact A₀.lev_one t

theorem levOK_add
    (hε_add : ∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (ε (x + y)) (hε (x + y)) P = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    {w w' : ℍ[ℚ, a₁, b₁]} (hw : LevOK A₀ R ε hε w) (hw' : LevOK A₀ R ε hε w') : LevOK A₀ R ε hε (w + w') := by
  refine ⟨R.add_mem hw.mem hw'.mem, fun t P hP => ?_⟩
  have h := hε_add ⟨w, hw.mem⟩ ⟨w', hw'.mem⟩ t P
  have : mapPt (ε ⟨w + w', R.add_mem hw.mem hw'.mem⟩) (hε _) P =
      A₀.L.mul t (pushPt (ε ⟨w, hw.mem⟩) (hε _) P) (pushPt (ε ⟨w', hw'.mem⟩) (hε _) P) := h
  rw [this]
  exact (A₀.lev_sub t _ _ (hw.lev hw.mem t P hP) (hw'.lev hw'.mem t P hP)).1

theorem levOK_neg
    (hε_add : ∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (ε (x + y)) (hε (x + y)) P = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    {w : ℍ[ℚ, a₁, b₁]} (hw : LevOK A₀ R ε hε w) : LevOK A₀ R ε hε (-w) := by
  refine ⟨R.neg_mem hw.mem, fun t P hP => ?_⟩
  have h := pushPt_map_neg A₀.L ε hε hε_add t P ⟨w, hw.mem⟩
  have : mapPt (ε ⟨-w, R.neg_mem hw.mem⟩) (hε _) P = A₀.L.inv t (pushPt (ε ⟨w, hw.mem⟩) (hε _) P) := h
  rw [this]
  exact (A₀.lev_sub t _ _ (hw.lev hw.mem t P hP) (hw.lev hw.mem t P hP)).2

theorem levOK_sub
    (hε_add : ∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (ε (x + y)) (hε (x + y)) P = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    {w w' : ℍ[ℚ, a₁, b₁]} (hw : LevOK A₀ R ε hε w) (hw' : LevOK A₀ R ε hε w') : LevOK A₀ R ε hε (w - w') := by
  rw [sub_eq_add_neg]
  exact levOK_add hε_add hw (levOK_neg hε_add hw')

theorem levOK_one (hR : IsOrder R) (hε : ∀ x : ↥R, ε x ≫ A₀.f = A₀.f) (hε_one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R, ε ⟨1, h⟩ = 𝟙 A₀.A) : LevOK A₀ R ε hε 1 := by
  refine ⟨hR.one_mem, fun t P hP => ?_⟩
  have : mapPt (ε ⟨1, hR.one_mem⟩) (hε _) P = P :=
    (pushPt_congr (hε_one hR.one_mem) (hε _) (Category.id_comp _) P).trans (pushPt_id _ P)
  rw [this]
  exact hP

theorem levOK_mul (hR : IsOrder R)
    (hε_mul : ∀ (x y : ↥R) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R),
      ε ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ε y ≫ ε x)
    {w w' : ℍ[ℚ, a₁, b₁]} (hw : LevOK A₀ R ε hε w) (hw' : LevOK A₀ R ε hε w') : LevOK A₀ R ε hε (w * w') := by
  refine ⟨hR.mul_mem hw.mem hw'.mem, fun t P hP => ?_⟩
  have hc : (ε ⟨w', hw'.mem⟩ ≫ ε ⟨w, hw.mem⟩) ≫ A₀.f = A₀.f := by rw [Category.assoc, hε, hε]
  have : mapPt (ε ⟨w * w', hR.mul_mem hw.mem hw'.mem⟩) (hε _) P =
      pushPt (ε ⟨w, hw.mem⟩) (hε _) (pushPt (ε ⟨w', hw'.mem⟩) (hε _) P) :=
    (pushPt_congr (hε_mul ⟨w, hw.mem⟩ ⟨w', hw'.mem⟩ _) (hε _) hc P).trans (pushPt_comp _ _ (hε _) (hε _) hc P)
  rw [this]
  exact hw.lev hw.mem t _ (hw'.lev hw'.mem t P hP)

theorem levOK_intCast (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (hR : IsOrder R)
    (hε_one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R, ε ⟨1, h⟩ = 𝟙 A₀.A)
    (hε_add : ∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (ε (x + y)) (hε (x + y)) P = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    (m : ℤ) : LevOK A₀ R ε hε ((m : ℚ) : ℍ[ℚ, a₁, b₁]) := by
  refine ⟨intCast_mem hR m, fun t P hP => ?_⟩
  have : mapPt (ε ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), intCast_mem hR m⟩) (hε _) P =
      pushPt (A₀.act ⟨((m : ℚ) : ℍ[ℚ, a, b]), hΛℤ m⟩) (A₀.act_over _) P :=
    pushPt_congr (eps_intCast hΛℤ hR hε_one hε_add m _) (hε _) (A₀.act_over _) P
  rw [this]
  exact A₀.lev_stable _ t P hP

def R₂sub (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (hR : IsOrder R)
    (hε_one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R, ε ⟨1, h⟩ = 𝟙 A₀.A)
    (hε_mul : ∀ (x y : ↥R) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R),
      ε ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (ε (x + y)) (hε (x + y)) P = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    (u : (ℍ[ℚ, a₁, b₁])ˣ) (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) : Submodule ℤ ℍ[ℚ, a₁, b₁] where
  carrier := {z | z ∈ R₁ ∧ LevOK A₀ R ε hε (cj u z)}
  add_mem' := by
    rintro z y ⟨hz, hz'⟩ ⟨hy, hy'⟩
    refine ⟨R₁.add_mem hz hy, ?_⟩
    rw [map_add]
    exact levOK_add hε_add hz' hy'
  zero_mem' := by
    refine ⟨R₁.zero_mem, ?_⟩
    rw [map_zero]
    exact levOK_zero hε_add
  smul_mem' := by
    rintro c z ⟨hz, hz'⟩
    refine ⟨R₁.smul_mem c hz, ?_⟩
    rw [map_zsmul, zsmul_eq_mul, ← coe_intCast]
    exact levOK_mul hR hε_mul (levOK_intCast hΛℤ hR hε_one hε_add c) hz'

def R₂'sub (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (u : (ℍ[ℚ, a₁, b₁])ˣ) (Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]) : Submodule ℤ ℍ[ℚ, a₁, b₁] where
  carrier := {z | z ∈ Λ₁s ∧ cj u z ∈ R}
  add_mem' := by
    rintro z y ⟨hz, hz'⟩ ⟨hy, hy'⟩
    refine ⟨Λ₁s.add_mem hz hy, ?_⟩
    rw [map_add]
    exact R.add_mem hz' hy'
  zero_mem' := ⟨Λ₁s.zero_mem, by rw [map_zero]; exact R.zero_mem⟩
  smul_mem' := by
    rintro c z ⟨hz, hz'⟩
    refine ⟨Λ₁s.smul_mem c hz, ?_⟩
    rw [map_zsmul]
    exact R.smul_mem c hz'

theorem mem_R₂sub {hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ} {hR : IsOrder R}
    {hε_one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R, ε ⟨1, h⟩ = 𝟙 A₀.A}
    {hε_mul : ∀ (x y : ↥R) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R),
      ε ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ε y ≫ ε x}
    {hε_add : ∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (ε (x + y)) (hε (x + y)) P = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P)}
    {u : (ℍ[ℚ, a₁, b₁])ˣ} {R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]} {z : ℍ[ℚ, a₁, b₁]} :
    z ∈ R₂sub hΛℤ hR hε_one hε_mul hε_add u R₁ ↔ z ∈ R₁ ∧ LevOK A₀ R ε hε (cj u z) := Iff.rfl

theorem mem_R₂'sub {u : (ℍ[ℚ, a₁, b₁])ˣ} {Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]} {z : ℍ[ℚ, a₁, b₁]} :
    z ∈ R₂'sub R u Λ₁s ↔ z ∈ Λ₁s ∧ cj u z ∈ R := Iff.rfl

def êR₂ {hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ} {hR : IsOrder R}
    {hε_one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R, ε ⟨1, h⟩ = 𝟙 A₀.A}
    {hε_mul : ∀ (x y : ↥R) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R),
      ε ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ε y ≫ ε x}
    {hε_add : ∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (ε (x + y)) (hε (x + y)) P = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P)}
    {u : (ℍ[ℚ, a₁, b₁])ˣ} {R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]}
    (z : ↥(R₂sub hΛℤ hR hε_one hε_mul hε_add u R₁)) : A₀.A ⟶ A₀.A :=
  ε ⟨cj u (z : ℍ[ℚ, a₁, b₁]), ((mem_R₂sub.mp z.2).2).mem⟩

def êR₂' (ε : ↥R → (A₀.A ⟶ A₀.A)) {u : (ℍ[ℚ, a₁, b₁])ˣ} {Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]}
    (z : ↥(R₂'sub R u Λ₁s)) : A₀.A ⟶ A₀.A :=
  ε ⟨cj u (z : ℍ[ℚ, a₁, b₁]), (mem_R₂'sub.mp z.2).2⟩

theorem isOrder_of_le_of_sat {S T : Submodule ℤ ℍ[ℚ, a₁, b₁]} (hT : IsOrder T) (hle : S ≤ T)
    (h1 : (1 : ℍ[ℚ, a₁, b₁]) ∈ S) (hmul : ∀ ⦃x y : ℍ[ℚ, a₁, b₁]⦄, x ∈ S → y ∈ S → x * y ∈ S)
    {r : ℕ} (hr : r ≠ 0) (hsat : ∀ z : ↥T, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) ∈ S) :
    IsOrder S where
  one_mem := h1
  mul_mem := hmul
  spanTop := by
    rw [eq_top_iff, ← hT.spanTop]
    refine Submodule.span_le.mpr fun z hz => ?_
    obtain ⟨c, hc⟩ := hsat ⟨z, hz⟩
    have hrc : ((r ^ c : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero c hr)
    have : z = ((r ^ c : ℕ) : ℚ)⁻¹ • (((r ^ c : ℕ) : ℚ) • z) := by
      rw [smul_smul, inv_mul_cancel₀ hrc, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hc)
  fg := hT.fg.of_le hle

end Frame

end CerednikDrinfeld.QM.FakeEllipticCurve.EndIsoExport

open CerednikDrinfeld.QM.FakeEllipticCurve.EndIsoExport in
theorem solution
    {r : ℕ} [Fact r.Prime]

    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord) {N : ℕ}

    {B : Type} [CommRing B] (hq : IsNilpotent (r : B))

    (A₀ : FakeEllipticCurve Λ N B) (X₀ : FormalODModule r B) (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (hθ₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    {a₁ b₁ : ℚ} (ha₁ : a₁ ≠ 0) (hb₁ : b₁ ≠ 0) (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR : IsOrder R)
    (ε : ↥R → (A₀.A ⟶ A₀.A)) (hε : ∀ x : ↥R, ε x ≫ A₀.f = A₀.f)
    (hε_hom : ∀ (x : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
      pushPt (ε x) (hε x) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_lin : ∀ (x : ↥R) (m : ↥Λ), A₀.act m ≫ ε x = ε x ≫ A₀.act m)
    (hε_one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R, ε ⟨1, h⟩ = 𝟙 A₀.A)
    (hε_mul : ∀ (x y : ↥R) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R),
      ε ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (ε (x + y)) (hε (x + y)) P = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))

    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (u : (ℍ[ℚ, a₁, b₁])ˣ)
    (e : ↥Γt → (A₀.A ⟶ A₀.A)) (he : ∀ γ, e γ ≫ A₀.f = A₀.f)
    (K : ↥Γt → ℕ) (x : ↥Γt → ↥R)
    (hx : ∀ γ : ↥Γt, (x γ : ℍ[ℚ, a₁, b₁]) =
      ((r ^ K γ : ℕ) : ℚ) • ((u⁻¹ * (γ : (ℍ[ℚ, a₁, b₁])ˣ) * u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]))
    (he_eq : ∀ γ : ↥Γt, e γ = ε (x γ))

    (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₁ : IsOrder R₁) (R' : Submodule ℤ ℍ[ℚ, a₁, b₁])
    (hR₁R' : ∀ z : ↥R₁, ∃ K : ℕ,
      ((r ^ K : ℕ) : ℚ) • (((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (z : ℍ[ℚ, a₁, b₁]) * ((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) ∈ R')
    (hR'R : ∀ y : ↥R', ∃ (K : ℕ) (hK : ((r ^ K : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]) ∈ R),
      FakeEllipticCurve.PreservesLevel A₀ A₀ (ε ⟨((r ^ K : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]), hK⟩) (hε _))

    (hε_inj : ∀ z y : ↥R, ε z = ε y → z = y)
    (hε_surj : ∀ (φ : A₀.A ⟶ A₀.A) (hφ : φ ≫ A₀.f = A₀.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
        mapPt φ hφ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ m : ↥Λ, A₀.act m ≫ φ = φ ≫ A₀.act m) → ∃ z : ↥R, φ = ε z)
    (hdivq : ∀ (q : ℕ), q.Prime → q ≠ r → ∀ (φ : A₀.A ⟶ A₀.A) (hφ : φ ≫ A₀.f = A₀.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
        mapPt φ hφ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ m : ↥Λ, A₀.act m ≫ φ = φ ≫ A₀.act m) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
        nsmulPt A₀.L t q P = A₀.L.one t → mapPt φ hφ P = A₀.L.one t) →
      ∃ (ψ : A₀.A ⟶ A₀.A) (hψ : ψ ≫ A₀.f = A₀.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
          mapPt ψ hψ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
        (∀ m : ↥Λ, A₀.act m ≫ ψ = ψ ≫ A₀.act m) ∧
        φ = A₀.act ⟨((q : ℤ) : ℚ), hΛℤ q⟩ ≫ ψ)
    (Λ₁ Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁s : IsMaximalOrder Λ₁s) (hR₁Λ₁s : R₁ ≤ Λ₁s) (htwin : Λ₁ ⊓ Λ₁s = R₁)
    (hΛ₁sR : ∀ z : ↥Λ₁s, ∃ K : ℕ,
      ((r ^ K : ℕ) : ℚ) • (((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (z : ℍ[ℚ, a₁, b₁]) * ((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) ∈ R)
    (hRΛ₁s : ∀ w : ↥R, ∃ K : ℕ,
      ((r ^ K : ℕ) : ℚ) • (((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (w : ℍ[ℚ, a₁, b₁]) * ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) ∈ Λ₁s)

    (K₀ : Type) [Field K₀] [CharZero K₀] (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) :
    ∃ (R₂ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₂ : R₂ ≤ R₁) (hR₂o : IsOrder R₂)
      (hR₂r : ∀ z : ↥R₁, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) ∈ R₂)
      (ê : ↥R₂ → (A₀.A ⟶ A₀.A)) (hê : ∀ z, ê z ≫ A₀.f = A₀.f),

      (∀ z : ↥R₂,
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
            mapPt (ê z) (hê z) (A₀.L.mul t P Q) = A₀.L.mul t (mapPt (ê z) (hê z) P) (mapPt (ê z) (hê z) Q)) ∧
        (∀ m : ↥Λ, A₀.act m ≫ ê z = ê z ≫ A₀.act m) ∧
        FakeEllipticCurve.PreservesLevel A₀ A₀ (ê z) (hê z)) ∧

      (∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R₂, ê ⟨1, h⟩ = 𝟙 A₀.A) ∧
      (∀ (z y : ↥R₂) (h : (z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂),
          ê ⟨(z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê y ≫ ê z) ∧
      (∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂), ê ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩) ∧

      (∀ (z y : ↥R₂) (nx : ℤ), (y : ℍ[ℚ, a₁, b₁]) = star (z : ℍ[ℚ, a₁, b₁]) → nrd (z : ℍ[ℚ, a₁, b₁]) = (nx : ℚ) →
          ê y ≫ ê z = A₀.act ⟨((nx : ℤ) : ℚ), hΛℤ nx⟩) ∧

      (∀ (γ : ↥Γt) (z : ↥R₂) (k : ℕ),
          (z : ℍ[ℚ, a₁, b₁]) = ((r ^ k : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) →
          ∃ i j : ℕ, e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ê z ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ∧

      (∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
        ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀,
          (∀ γ : ↥Γt, ∃ (εX : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
            (∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ),
                J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
                θ₀ B' (fun i => MvFormalGroup.nilEval m ((εX : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                  mapPt (e γ) (he γ) (θ₀ B' s)) ∧
            E₀ εX = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
              ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) ∧
          (∀ z : ↥R₂, ∃ (εX : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kx : ℤ),
            (∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ),
                J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
                θ₀ B' (fun i => MvFormalGroup.nilEval m ((εX : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                  mapPt (ê z) (hê z) (θ₀ B' s)) ∧
            E₀ εX = ((r : K₀) ^ kx) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ (z : ℍ[ℚ, a₁, b₁]) *
              ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)))) ∧

      (∀ z : ↥R₂, star (z : ℍ[ℚ, a₁, b₁]) ∈ R₂) ∧

      (∃ (Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁s : IsMaximalOrder Λ₁s) (hR₁Λ₁s : R₁ ≤ Λ₁s) (htwin : Λ₁ ⊓ Λ₁s = R₁)
          (R₂' : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₂' : R₂' ≤ Λ₁s) (hR₂'o : IsOrder R₂')
          (hR₂'r : ∀ z : ↥Λ₁s, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) ∈ R₂') (hR₂R₂' : R₂ ≤ R₂')
          (ê' : ↥R₂' → (A₀.A ⟶ A₀.A)) (hê' : ∀ z, ê' z ≫ A₀.f = A₀.f),

        (∀ z : ↥R₂',
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
              mapPt (ê' z) (hê' z) (A₀.L.mul t P Q) = A₀.L.mul t (mapPt (ê' z) (hê' z) P) (mapPt (ê' z) (hê' z) Q)) ∧
          (∀ m : ↥Λ, A₀.act m ≫ ê' z = ê' z ≫ A₀.act m)) ∧

        (∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R₂', ê' ⟨1, h⟩ = 𝟙 A₀.A) ∧
        (∀ (z y : ↥R₂') (h : (z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂'),
            ê' ⟨(z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê' y ≫ ê' z) ∧
        (∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂'), ê' ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩) ∧

        (∀ (z y : ↥R₂') (nz : ℤ), (y : ℍ[ℚ, a₁, b₁]) = star (z : ℍ[ℚ, a₁, b₁]) → nrd (z : ℍ[ℚ, a₁, b₁]) = (nz : ℚ) →
            ê' y ≫ ê' z = A₀.act ⟨((nz : ℤ) : ℚ), hΛℤ nz⟩) ∧

        (∀ z : ↥R₂, ê' ⟨(z : ℍ[ℚ, a₁, b₁]), hR₂R₂' z.2⟩ = ê z) ∧

        (∀ z : ↥R₂', star (z : ℍ[ℚ, a₁, b₁]) ∈ R₂') ∧
        (∀ z y : ↥R₂', ê' z = ê' y → z = y) ∧

        (∀ (q : ℕ), q.Prime → q ≠ r → ∀ z : ↥R₂',
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
              nsmulPt A₀.L t q P = A₀.L.one t → mapPt (ê' z) (hê' z) P = A₀.L.one t) →
          ∃ (K : ℕ) (y : ↥Λ₁s), ((r ^ K : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) = (q : ℚ) • (y : ℍ[ℚ, a₁, b₁]))) := by
  classical
  have h1R : (1 : ℍ[ℚ, a₁, b₁]) ∈ R := hR.one_mem
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := one_mem_Λ hΛℤ
  have hr0 : r ≠ 0 := (Fact.out : r.Prime).ne_zero
  have act_rpow_zero : A₀.act ⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = 𝟙 A₀.A := by
    have : (⟨((((r ^ 0 : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]), hΛℤ _⟩ : ↥Λ) = ⟨1, h1Λ⟩ := Subtype.ext (by simp)
    rw [this]
    exact A₀.act_one _

  have hR₂le : R₂sub hΛℤ hR hε_one hε_mul hε_add u R₁ ≤ R₁ := fun z hz => (mem_R₂sub.mp hz).1
  have hR₂sat : ∀ z : ↥R₁, ∃ c : ℕ,
      ((r ^ c : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) ∈ R₂sub hΛℤ hR hε_one hε_mul hε_add u R₁ := by
    intro z
    obtain ⟨K₁, hK₁⟩ := hR₁R' z
    obtain ⟨K₂, hK₂, hlev⟩ := hR'R ⟨_, hK₁⟩
    refine ⟨K₂ + K₁, mem_R₂sub.mpr ⟨?_, ?_⟩⟩
    · rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem z.2 _
    · have e : cj u (((r ^ (K₂ + K₁) : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁])) =
          ((r ^ K₂ : ℕ) : ℚ) • (((r ^ K₁ : ℕ) : ℚ) •
            (((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (z : ℍ[ℚ, a₁, b₁]) * ((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]))) := by
        rw [map_smul, cj_apply, smul_smul]
        congr 1
        push_cast
        ring
      exact levOK_congr e.symm ⟨hK₂, hlev⟩
  have hR₂ord : IsOrder (R₂sub hΛℤ hR hε_one hε_mul hε_add u R₁) :=
    isOrder_of_le_of_sat hR₁ hR₂le
      (mem_R₂sub.mpr ⟨hR₁.one_mem, by rw [map_one]; exact levOK_one hR hε hε_one⟩)
      (fun x y hx hy => mem_R₂sub.mpr ⟨hR₁.mul_mem (mem_R₂sub.mp hx).1 (mem_R₂sub.mp hy).1, by
        rw [map_mul]; exact levOK_mul hR hε_mul (mem_R₂sub.mp hx).2 (mem_R₂sub.mp hy).2⟩)
      hr0 hR₂sat

  have hΛ₁so : IsOrder Λ₁s := hΛ₁s.isOrder
  have hR₂'le : R₂'sub R u Λ₁s ≤ Λ₁s := fun z hz => (mem_R₂'sub.mp hz).1
  have hR₂'sat : ∀ z : ↥Λ₁s, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) ∈ R₂'sub R u Λ₁s := by
    intro z
    obtain ⟨K₁, hK₁⟩ := hΛ₁sR z
    refine ⟨K₁, mem_R₂'sub.mpr ⟨?_, ?_⟩⟩
    · rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem z.2 _
    · rw [map_smul]
      exact hK₁
  have hR₂'ord : IsOrder (R₂'sub R u Λ₁s) :=
    isOrder_of_le_of_sat hΛ₁so hR₂'le
      (mem_R₂'sub.mpr ⟨hΛ₁so.one_mem, by rw [map_one]; exact hR.one_mem⟩)
      (fun x y hx hy => mem_R₂'sub.mpr ⟨hΛ₁so.mul_mem (mem_R₂'sub.mp hx).1 (mem_R₂'sub.mp hy).1, by
        rw [map_mul]; exact hR.mul_mem (mem_R₂'sub.mp hx).2 (mem_R₂'sub.mp hy).2⟩)
      hr0 hR₂'sat
  have hR₂R₂' : R₂sub hΛℤ hR hε_one hε_mul hε_add u R₁ ≤ R₂'sub R u Λ₁s :=
    fun z hz => mem_R₂'sub.mpr ⟨hR₁Λ₁s (mem_R₂sub.mp hz).1, (mem_R₂sub.mp hz).2.mem⟩

  refine ⟨R₂sub hΛℤ hR hε_one hε_mul hε_add u R₁, hR₂le, hR₂ord, hR₂sat, êR₂, fun z => hε _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro z
    exact ⟨fun t P Q => hε_hom _ t P Q, fun m => hε_lin _ m, ((mem_R₂sub.mp z.2).2).lev _⟩
  ·
    intro h
    have e1 : (⟨cj u 1, ((mem_R₂sub.mp h).2).mem⟩ : ↥R) = ⟨1, h1R⟩ := Subtype.ext (map_one _)
    exact (congrArg ε e1).trans (hε_one _)
  ·
    intro z y h
    have hz := ((mem_R₂sub.mp z.2).2).mem
    have hy := ((mem_R₂sub.mp y.2).2).mem
    have e1 : (⟨cj u ((z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁])), ((mem_R₂sub.mp h).2).mem⟩ : ↥R) =
        ⟨cj u (z : ℍ[ℚ, a₁, b₁]) * cj u (y : ℍ[ℚ, a₁, b₁]), hR.mul_mem hz hy⟩ := Subtype.ext (map_mul _ _ _)
    exact (congrArg ε e1).trans (hε_mul ⟨_, hz⟩ ⟨_, hy⟩ _)
  ·
    intro m h
    have e1 : (⟨cj u ((m : ℚ) : ℍ[ℚ, a₁, b₁]), ((mem_R₂sub.mp h).2).mem⟩ : ↥R) =
        ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), intCast_mem hR m⟩ := Subtype.ext (cj_intCast u m)
    exact (congrArg ε e1).trans (eps_intCast hΛℤ hR hε_one hε_add m _)
  ·
    intro z y nx hy hn
    have hz := ((mem_R₂sub.mp z.2).2).mem
    have hy' := ((mem_R₂sub.mp y.2).2).mem
    have e1 : (⟨cj u (z : ℍ[ℚ, a₁, b₁]) * cj u (y : ℍ[ℚ, a₁, b₁]), hR.mul_mem hz hy'⟩ : ↥R) =
        ⟨((nx : ℚ) : ℍ[ℚ, a₁, b₁]), intCast_mem hR nx⟩ := by
      apply Subtype.ext
      show cj u (z : ℍ[ℚ, a₁, b₁]) * cj u (y : ℍ[ℚ, a₁, b₁]) = ((nx : ℚ) : ℍ[ℚ, a₁, b₁])
      rw [← map_mul, hy, mul_star_eq_coe_nrd, hn]
      exact cj_ratCast u _
    calc êR₂ y ≫ êR₂ z = ε ⟨cj u (z : ℍ[ℚ, a₁, b₁]) * cj u (y : ℍ[ℚ, a₁, b₁]), hR.mul_mem hz hy'⟩ :=
          (hε_mul ⟨_, hz⟩ ⟨_, hy'⟩ (hR.mul_mem hz hy')).symm
      _ = ε ⟨((nx : ℚ) : ℍ[ℚ, a₁, b₁]), intCast_mem hR nx⟩ := congrArg ε e1
      _ = A₀.act ⟨((nx : ℤ) : ℚ), hΛℤ nx⟩ := eps_intCast hΛℤ hR hε_one hε_add nx _
  ·
    intro γ z k hzk
    refine ⟨k, K γ, ?_⟩
    have hz := ((mem_R₂sub.mp z.2).2).mem
    have hk : ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R := intCast_mem hR _
    have hK : ((((r ^ K γ : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R := intCast_mem hR _
    rw [he_eq γ, ← eps_intCast hΛℤ hR hε_one hε_add ((r ^ k : ℕ) : ℤ) hk,
      ← eps_intCast hΛℤ hR hε_one hε_add ((r ^ K γ : ℕ) : ℤ) hK,
      ← hε_mul ⟨_, hk⟩ (x γ) (hR.mul_mem hk (x γ).2)]
    show _ = ε ⟨cj u (z : ℍ[ℚ, a₁, b₁]), hz⟩ ≫ ε ⟨_, hK⟩
    rw [← hε_mul ⟨_, hK⟩ ⟨cj u (z : ℍ[ℚ, a₁, b₁]), hz⟩ (hR.mul_mem hK hz)]
    congr 1
    apply Subtype.ext
    show ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a₁, b₁]) * (x γ : ℍ[ℚ, a₁, b₁]) =
      ((((r ^ K γ : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a₁, b₁]) * cj u (z : ℍ[ℚ, a₁, b₁])
    rw [hx γ, cj_units, hzk, map_smul, coe_mul_eq_smul, coe_mul_eq_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  ·
    intro E₀ _hinj
    have hmul' : ∀ (x y : ↥R) (hxy : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R)
        {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
        nsmulPt A₀.L t (r ^ 0) (pushPt (ε ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), hxy⟩) (hε _) P) =
          pushPt (ε x) (hε x) (pushPt (ε y) (hε y) P) := by
      intro x y hxy T t P
      rw [pow_zero]
      show A₀.L.mul t (A₀.L.one t) _ = _
      rw [A₀.L.one_mul]
      have hc : (ε y ≫ ε x) ≫ A₀.f = A₀.f := by rw [Category.assoc, hε, hε]
      rw [pushPt_congr (hε_mul x y hxy) (hε _) hc P]
      exact pushPt_comp _ _ (hε y) (hε x) hc P
    have hone' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
        pushPt (ε ⟨1, hR.one_mem⟩) (hε _) P = nsmulPt A₀.L t (r ^ 0) P := by
      intro T t P
      rw [pow_zero]
      show _ = A₀.L.mul t (A₀.L.one t) P
      rw [A₀.L.one_mul, pushPt_congr (hε_one hR.one_mem) (hε _) (Category.id_comp _) P, pushPt_id]
    obtain ⟨g, hg⟩ :=
      exists_generalLinearGroup_forall_exists_centralizer_isFormalCompletionAlong_and_apply_eq_zpow_smul_conj
        hΛℤ coord hcoord hq A₀ X₀ θ₀ hθ₀ ha₁ hb₁ R hR 0 ε hε hε_hom hε_lin hε_add hmul' hone'
        (I := ↥Γt ⊕ ↥(R₂sub hΛℤ hR hε_one hε_mul hε_add u R₁))
        (Sum.elim (fun γ : ↥Γt => cj u ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]))
          (fun z : ↥(R₂sub hΛℤ hR hε_one hε_mul hε_add u R₁) => cj u (z : ℍ[ℚ, a₁, b₁])))
        (fun i => ε (Sum.elim x (fun z : ↥(R₂sub hΛℤ hR hε_one hε_mul hε_add u R₁) =>
          (⟨cj u (z : ℍ[ℚ, a₁, b₁]), ((mem_R₂sub.mp z.2).2).mem⟩ : ↥R)) i))
        (fun i => hε _) (fun i => hε_hom _) (fun i => hε_lin _)
        (by
          rintro (γ | z)
          · refine ⟨K γ, 0, x γ, ?_, ?_⟩
            · simp only [Sum.elim_inl]
              rw [hx γ, cj_units]
            · simp only [Sum.elim_inl]
              rw [act_rpow_zero]
              exact Category.comp_id _
          · refine ⟨0, 0, ⟨cj u (z : ℍ[ℚ, a₁, b₁]), ((mem_R₂sub.mp z.2).2).mem⟩, ?_, ?_⟩
            · simp
            · simp only [Sum.elim_inr]
              rw [act_rpow_zero]
              exact Category.comp_id _)
        K₀ ι₀ E₀

    obtain ⟨gu, hgu, hgu'⟩ : ∃ gu : Matrix.GeneralLinearGroup (Fin 2) K₀,
        (gu : Matrix (Fin 2) (Fin 2) K₀) = ι₀ ((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ∧
        ((gu⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) =
          ι₀ ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) :=
      ⟨⟨ι₀ ((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]), ι₀ ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]),
        by rw [← map_mul, Units.mul_inv, map_one], by rw [← map_mul, Units.inv_mul, map_one]⟩, rfl, rfl⟩
    have hconj : ∀ y : ℍ[ℚ, a₁, b₁],
        (g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ (cj u y) * ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) =
          ((g * gu⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) * ι₀ y *
            (((g * gu⁻¹)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) := by
      intro y
      rw [mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, hgu, hgu', cj_apply, map_mul, map_mul]
      simp only [mul_assoc]
    refine ⟨g * gu⁻¹, fun γ => ?_, fun z => ?_⟩
    · obtain ⟨εX, ki, hcomp, hmat⟩ := hg (Sum.inl γ)
      refine ⟨εX, ki, fun B' _ _ J m hJ s hs => ?_, ?_⟩
      · rw [mapPt_congr (he_eq γ) (he γ) (hε (x γ))]
        exact hcomp B' J m hJ s hs
      · rw [hmat]
        simp only [Sum.elim_inl]
        rw [hconj]
    · obtain ⟨εX, ki, hcomp, hmat⟩ := hg (Sum.inr z)
      refine ⟨εX, ki, fun B' _ _ J m hJ s hs => hcomp B' J m hJ s hs, ?_⟩
      rw [hmat]
      simp only [Sum.elim_inr]
      rw [hconj]
  ·
    intro z
    obtain ⟨hz1, hz2⟩ := mem_R₂sub.mp z.2
    obtain ⟨hstar, t, n, ht, -⟩ := IsOrder.star_mem_and_exists_int_trd_nrd hR₁ hz1
    have hs : star (z : ℍ[ℚ, a₁, b₁]) = ((t : ℚ) : ℍ[ℚ, a₁, b₁]) - z :=
      eq_sub_of_add_eq' (by rw [add_star_eq_coe_trd, ht])
    refine mem_R₂sub.mpr ⟨hstar, ?_⟩
    rw [hs, map_sub, cj_intCast]
    exact levOK_sub hε_add (levOK_intCast hΛℤ hR hε_one hε_add t) hz2
  ·
    refine ⟨Λ₁s, hΛ₁s, hR₁Λ₁s, htwin, R₂'sub R u Λ₁s, hR₂'le, hR₂'ord, hR₂'sat, hR₂R₂', êR₂' ε, fun z => hε _,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    ·
      intro z
      exact ⟨fun t P Q => hε_hom _ t P Q, fun m => hε_lin _ m⟩
    ·
      intro h
      have e1 : (⟨cj u 1, (mem_R₂'sub.mp h).2⟩ : ↥R) = ⟨1, h1R⟩ := Subtype.ext (map_one _)
      exact (congrArg ε e1).trans (hε_one _)
    ·
      intro z y h
      have hz := (mem_R₂'sub.mp z.2).2
      have hy := (mem_R₂'sub.mp y.2).2
      have e1 : (⟨cj u ((z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁])), (mem_R₂'sub.mp h).2⟩ : ↥R) =
          ⟨cj u (z : ℍ[ℚ, a₁, b₁]) * cj u (y : ℍ[ℚ, a₁, b₁]), hR.mul_mem hz hy⟩ := Subtype.ext (map_mul _ _ _)
      exact (congrArg ε e1).trans (hε_mul ⟨_, hz⟩ ⟨_, hy⟩ _)
    ·
      intro m h
      have e1 : (⟨cj u ((m : ℚ) : ℍ[ℚ, a₁, b₁]), (mem_R₂'sub.mp h).2⟩ : ↥R) =
          ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), intCast_mem hR m⟩ := Subtype.ext (cj_intCast u m)
      exact (congrArg ε e1).trans (eps_intCast hΛℤ hR hε_one hε_add m _)
    ·
      intro z y nz hy hn
      have hz := (mem_R₂'sub.mp z.2).2
      have hy' := (mem_R₂'sub.mp y.2).2
      have e1 : (⟨cj u (z : ℍ[ℚ, a₁, b₁]) * cj u (y : ℍ[ℚ, a₁, b₁]), hR.mul_mem hz hy'⟩ : ↥R) =
          ⟨((nz : ℚ) : ℍ[ℚ, a₁, b₁]), intCast_mem hR nz⟩ := by
        apply Subtype.ext
        show cj u (z : ℍ[ℚ, a₁, b₁]) * cj u (y : ℍ[ℚ, a₁, b₁]) = ((nz : ℚ) : ℍ[ℚ, a₁, b₁])
        rw [← map_mul, hy, mul_star_eq_coe_nrd, hn]
        exact cj_ratCast u _
      calc êR₂' ε y ≫ êR₂' ε z = ε ⟨cj u (z : ℍ[ℚ, a₁, b₁]) * cj u (y : ℍ[ℚ, a₁, b₁]), hR.mul_mem hz hy'⟩ :=
            (hε_mul ⟨_, hz⟩ ⟨_, hy'⟩ (hR.mul_mem hz hy')).symm
        _ = ε ⟨((nz : ℚ) : ℍ[ℚ, a₁, b₁]), intCast_mem hR nz⟩ := congrArg ε e1
        _ = A₀.act ⟨((nz : ℤ) : ℚ), hΛℤ nz⟩ := eps_intCast hΛℤ hR hε_one hε_add nz _
    ·
      intro z
      rfl
    ·
      intro z
      obtain ⟨hz1, hz2⟩ := mem_R₂'sub.mp z.2
      obtain ⟨hstar, t, n, ht, -⟩ := IsOrder.star_mem_and_exists_int_trd_nrd hΛ₁so hz1
      have hs : star (z : ℍ[ℚ, a₁, b₁]) = ((t : ℚ) : ℍ[ℚ, a₁, b₁]) - z :=
        eq_sub_of_add_eq' (by rw [add_star_eq_coe_trd, ht])
      refine mem_R₂'sub.mpr ⟨hstar, ?_⟩
      rw [hs, map_sub, cj_intCast]
      exact R.sub_mem (intCast_mem hR t) hz2
    ·
      intro z y h
      apply Subtype.ext
      apply cj_injective u
      exact congrArg Subtype.val (hε_inj ⟨_, (mem_R₂'sub.mp z.2).2⟩ ⟨_, (mem_R₂'sub.mp y.2).2⟩ h)
    ·
      intro q hqp hqr z hkill
      obtain ⟨hz1, hz2⟩ := mem_R₂'sub.mp z.2
      obtain ⟨ψ, hψ, hψhom, hψlin, hfac⟩ :=
        hdivq q hqp hqr (ε ⟨cj u (z : ℍ[ℚ, a₁, b₁]), hz2⟩) (hε _) (fun t P Q => hε_hom _ t P Q)
          (fun m => hε_lin _ m) hkill
      obtain ⟨w', hw'⟩ := hε_surj ψ hψ hψhom hψlin
      have hqR : ((((q : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R := intCast_mem hR q
      have key : ε ⟨cj u (z : ℍ[ℚ, a₁, b₁]), hz2⟩ =
          ε ⟨(w' : ℍ[ℚ, a₁, b₁]) * ((((q : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a₁, b₁]), hR.mul_mem w'.2 hqR⟩ := by
        rw [hfac, hw', ← eps_intCast hΛℤ hR hε_one hε_add (q : ℤ) hqR]
        exact (hε_mul w' ⟨_, hqR⟩ (hR.mul_mem w'.2 hqR)).symm
      have hval : cj u (z : ℍ[ℚ, a₁, b₁]) = (w' : ℍ[ℚ, a₁, b₁]) * ((((q : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a₁, b₁]) :=
        congrArg Subtype.val (hε_inj _ _ key)
      obtain ⟨K₁, hK₁⟩ := hRΛ₁s w'
      refine ⟨K₁, ⟨_, hK₁⟩, ?_⟩
      have hz : (z : ℍ[ℚ, a₁, b₁]) =
          ((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * cj u (z : ℍ[ℚ, a₁, b₁]) * ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) :=
        (uncj u _).symm
      rw [hz, hval, Int.cast_natCast, ← coe_commutes, coe_mul_eq_smul, mul_smul_comm, smul_mul_assoc]
      exact smul_comm _ _ _

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective (solution)
