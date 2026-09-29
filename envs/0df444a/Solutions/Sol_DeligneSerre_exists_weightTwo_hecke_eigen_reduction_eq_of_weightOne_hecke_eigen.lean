-- Prove2me | solution 1 for DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/eacae073-0251-53fd-b8ee-38e2f128a6ce

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen
import Theorems.Thm_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd
import Theorems.Thm_DeligneSerre_exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0"

set_option autoImplicit false

open CongruenceSubgroup UpperHalfPlane Polynomial
open scoped MatrixGroups

namespace DeligneSerreW1W2

open ModularFormClass

open ModularFormClass

theorem gamma1_le_of_dvd {A B : ℕ} (h : A ∣ B) : Gamma1 B ≤ Gamma1 A := by
  intro γ hγ
  rw [Gamma1_mem] at hγ ⊢
  obtain ⟨h00, h11, h10⟩ := hγ
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (ZMod.castHom h (ZMod A)) h00
    rwa [map_one, map_intCast] at this
  · have := congrArg (ZMod.castHom h (ZMod A)) h11
    rwa [map_one, map_intCast] at this
  · have := congrArg (ZMod.castHom h (ZMod A)) h10
    rwa [map_zero, map_intCast] at this

theorem gamma0_le_of_dvd {A B : ℕ} (h : A ∣ B) : Gamma0 B ≤ Gamma0 A := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  have := congrArg (ZMod.castHom h (ZMod A)) hγ
  rwa [map_zero, map_intCast] at this

theorem gamma1GL_le_of_dvd {A B : ℕ} (h : A ∣ B) :
    ((Gamma1 B : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma1 A : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rintro _ ⟨γ, hγ, rfl⟩
  exact ⟨γ, gamma1_le_of_dvd h hγ, rfl⟩

noncomputable def restrictMF {A B : ℕ} [NeZero A] [NeZero B] (h : A ∣ B) {k : ℤ}
    (E : ModularForm (Gamma1 A) k) : ModularForm (Gamma1 B) k where
  toFun := E
  slash_action_eq' γ hγ := E.slash_action_eq' γ (gamma1GL_le_of_dvd h hγ)
  holo' := E.holo'
  bdd_at_cusps' hc := E.bdd_at_cusps'
    ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).2
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).1 hc))

@[scoped simp] theorem coe_restrictMF {A B : ℕ} [NeZero A] [NeZero B] (h : A ∣ B) {k : ℤ}
    (E : ModularForm (Gamma1 A) k) : ⇑(restrictMF h E) = ⇑E := rfl

noncomputable def restrictCF {A B : ℕ} [NeZero A] [NeZero B] (h : A ∣ B) {k : ℤ}
    (f : CuspForm (Gamma1 A) k) : CuspForm (Gamma1 B) k where
  toFun := f
  slash_action_eq' γ hγ := f.slash_action_eq' γ (gamma1GL_le_of_dvd h hγ)
  holo' := f.holo'
  zero_at_cusps' hc := f.zero_at_cusps'
    ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).2
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).1 hc))

@[scoped simp] theorem coe_restrictCF {A B : ℕ} [NeZero A] [NeZero B] (h : A ∣ B) {k : ℤ}
    (f : CuspForm (Gamma1 A) k) : ⇑(restrictCF h f) = ⇑f := rfl

theorem one_mem_strictPeriods_gamma1 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem isUnit_entry_of_mem_gamma0 {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    IsUnit (((γ 1 1 : ℤ) : ZMod M)) := by
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at this
    exact this
  rw [Gamma0_mem] at hγ
  have h : ((γ 0 0 : ℤ) : ZMod M) * ((γ 1 1 : ℤ) : ZMod M) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod M)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at this
    rw [hγ, mul_zero, sub_zero] at this
    exact this
  exact IsUnit.of_mul_eq_one_right _ h

theorem changeLevel_apply_entry {A M : ℕ} (h : A ∣ M) (χ : DirichletCharacter ℂ A)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    DirichletCharacter.changeLevel h χ ((γ 1 1 : ℤ) : ZMod M) = χ ((γ 1 1 : ℤ) : ZMod A) := by
  have hu := isUnit_entry_of_mem_gamma0 hγ
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ h hu.unit
  rw [IsUnit.unit_spec] at this
  rw [this, ZMod.cast_intCast h]

theorem changeLevel_natCast_of_not_dvd' {A M : ℕ} (h : A ∣ M) (χ : DirichletCharacter ℂ A)
    {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) :
    DirichletCharacter.changeLevel h χ (p : ZMod M) = χ (p : ZMod A) := by
  have hcop : p.Coprime M := (Nat.Prime.coprime_iff_not_dvd hp).2 hpM
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ h (ZMod.unitOfCoprime p hcop)
  simp only [ZMod.coe_unitOfCoprime] at this
  rw [this, ZMod.cast_natCast h]

theorem changeLevel_mem' {A M : ℕ} (h : A ∣ M) (χ : DirichletCharacter ℂ A)
    (R : Subalgebra ℤ ℂ) (hχ : ∀ x : ZMod A, χ x ∈ R) (x : ZMod M) :
    DirichletCharacter.changeLevel h χ x ∈ R := by
  by_cases hx : IsUnit x
  · have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ h hx.unit
    rw [IsUnit.unit_spec] at this
    rw [this]
    exact hχ _
  · rw [MulChar.map_nonunit _ hx]
    exact zero_mem R

open scoped ModularForm in
theorem hasNebentypus_of_hecke {N : ℕ} [NeZero N] (ε : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        qCoeff f (p * n) + ε (p : ZMod N) * (if p ∣ n then qCoeff f (n / p) else 0) =
          qCoeff f p * qCoeff f n) :
    CuspForm.HasNebentypus ε f := by
  have heig : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ lam : ℂ, ∀ n : ℕ,
      qCoeff (⇑f) (n * p) + ε (p : ZMod N) * (p : ℂ) ^ ((1 : ℤ) - 1) *
          (if p ∣ n then qCoeff (⇑f) (n / p) else 0) = lam * qCoeff (⇑f) n := by
    intro p hp hpN
    refine ⟨qCoeff f p, fun n => ?_⟩
    rw [mul_comm n p, sub_self, zpow_zero, mul_one]
    exact hT p hp hpN n
  intro γ hγ τ
  have hslash := CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen 1 f ε heig γ hγ
  have hs : ((⇑f : ℍ → ℂ) ∣[(1 : ℤ)] γ) τ = f (γ • τ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-(1 : ℤ)) :=
    ModularForm.SL_slash_apply (f := ⇑f) (k := 1) γ τ
  have hpt := congrFun hslash τ
  rw [hs, Pi.smul_apply, smul_eq_mul] at hpt
  have hden : denom (γ : GL (Fin 2) ℝ) τ = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
    rw [ModularGroup.denom_apply]
  have hne : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ τ
  rw [hden] at hpt
  have := congrArg (fun z => z * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (1 : ℤ)) hpt
  rw [mul_assoc, ← zpow_add₀ hne, neg_add_cancel, zpow_zero, mul_one] at this
  rw [this]
  ring

section Loc

variable (R : Subalgebra ℤ ℂ) {κ : Type} [Field κ] (φ : R →+* κ)

def locKer : Subalgebra ℤ ℂ where
  carrier := {z | ∃ (s : ℂ) (hs : s ∈ R), φ ⟨s, hs⟩ ≠ 0 ∧ s * z ∈ R}
  mul_mem' := by
    rintro x y ⟨s, hs, hs0, hsx⟩ ⟨t, ht, ht0, hty⟩
    refine ⟨s * t, mul_mem hs ht, ?_, ?_⟩
    · have : (⟨s * t, mul_mem hs ht⟩ : R) = ⟨s, hs⟩ * ⟨t, ht⟩ := rfl
      rw [this, map_mul]
      exact mul_ne_zero hs0 ht0
    · have : s * t * (x * y) = (s * x) * (t * y) := by ring
      rw [this]
      exact mul_mem hsx hty
  add_mem' := by
    rintro x y ⟨s, hs, hs0, hsx⟩ ⟨t, ht, ht0, hty⟩
    refine ⟨s * t, mul_mem hs ht, ?_, ?_⟩
    · have : (⟨s * t, mul_mem hs ht⟩ : R) = ⟨s, hs⟩ * ⟨t, ht⟩ := rfl
      rw [this, map_mul]
      exact mul_ne_zero hs0 ht0
    · have : s * t * (x + y) = t * (s * x) + s * (t * y) := by ring
      rw [this]
      exact add_mem (mul_mem ht hsx) (mul_mem hs hty)
  algebraMap_mem' := by
    intro z
    refine ⟨1, one_mem R, ?_, ?_⟩
    · have : (⟨(1 : ℂ), one_mem R⟩ : R) = 1 := rfl
      rw [this, map_one]; exact one_ne_zero
    · rw [one_mul]; exact R.algebraMap_mem z

variable {R φ}

theorem mem_locKer_iff (z : ℂ) :
    z ∈ locKer R φ ↔ ∃ (s : ℂ) (hs : s ∈ R), φ ⟨s, hs⟩ ≠ 0 ∧ s * z ∈ R := Iff.rfl

theorem mem_locKer_of_mem {z : ℂ} (hz : z ∈ R) : z ∈ locKer R φ :=
  ⟨1, one_mem R, by
    have : (⟨(1 : ℂ), one_mem R⟩ : R) = 1 := rfl
    rw [this, map_one]; exact one_ne_zero, by rw [one_mul]; exact hz⟩

theorem le_locKer : R ≤ locKer R φ := fun _ hz => mem_locKer_of_mem hz

noncomputable def locKerExt (z : locKer R φ) : κ :=
  φ ⟨z.2.choose * z, z.2.choose_spec.2.2⟩ * (φ ⟨z.2.choose, z.2.choose_spec.1⟩)⁻¹

theorem map_mul_mk (s y : ℂ) (hs : s ∈ R) (hy : y ∈ R) (hsy : s * y ∈ R) :
    φ ⟨s * y, hsy⟩ = φ ⟨s, hs⟩ * φ ⟨y, hy⟩ := by
  have : (⟨s * y, hsy⟩ : R) = ⟨s, hs⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul]

theorem locKerExt_eq (z : locKer R φ) {s : ℂ} (hs : s ∈ R) (hs0 : φ ⟨s, hs⟩ ≠ 0)
    (hsz : s * (z : ℂ) ∈ R) :
    locKerExt z = φ ⟨s * z, hsz⟩ * (φ ⟨s, hs⟩)⁻¹ := by
  unfold locKerExt
  set s₀ := z.2.choose with hs₀_def
  have hs₀ : s₀ ∈ R := z.2.choose_spec.1
  have hs₀0 : φ ⟨s₀, hs₀⟩ ≠ 0 := z.2.choose_spec.2.1
  have hs₀z : s₀ * (z : ℂ) ∈ R := z.2.choose_spec.2.2
  rw [mul_inv_eq_iff_eq_mul₀ hs₀0, mul_assoc, mul_comm ((φ ⟨s, hs⟩)⁻¹), ← mul_assoc,
    eq_mul_inv_iff_mul_eq₀ hs0]

  have hmem : s * (s₀ * (z : ℂ)) ∈ R := mul_mem hs hs₀z
  have h1 : φ ⟨s₀ * z, hs₀z⟩ * φ ⟨s, hs⟩ = φ ⟨s * (s₀ * z), hmem⟩ := by
    rw [map_mul_mk s _ hs hs₀z hmem, mul_comm]
  have hmem' : s₀ * (s * (z : ℂ)) ∈ R := mul_mem hs₀ hsz
  have h2 : φ ⟨s * z, hsz⟩ * φ ⟨s₀, hs₀⟩ = φ ⟨s₀ * (s * z), hmem'⟩ := by
    rw [map_mul_mk s₀ _ hs₀ hsz hmem', mul_comm]
  rw [h1, h2]
  congr 1
  apply Subtype.ext
  change s * (s₀ * (z : ℂ)) = s₀ * (s * z)
  ring

theorem locKerExt_of_mem {z : ℂ} (hz : z ∈ R) :
    locKerExt (⟨z, mem_locKer_of_mem hz⟩ : locKer R φ) = φ ⟨z, hz⟩ := by
  have h1 : φ ⟨(1 : ℂ), one_mem R⟩ ≠ 0 := by
    have : (⟨(1 : ℂ), one_mem R⟩ : R) = 1 := rfl
    rw [this, map_one]; exact one_ne_zero
  have hz1 : (1 : ℂ) * z ∈ R := by rw [one_mul]; exact hz
  rw [locKerExt_eq (φ := φ) ⟨z, mem_locKer_of_mem hz⟩ (one_mem R) h1 hz1]
  have : (⟨(1 : ℂ), one_mem R⟩ : R) = 1 := rfl
  rw [this, map_one, inv_one, mul_one]
  congr 1
  apply Subtype.ext
  simp

noncomputable def locKerHom : locKer R φ →+* κ where
  toFun := locKerExt
  map_one' := by
    have := locKerExt_of_mem (φ := φ) (one_mem R)
    rw [show (1 : locKer R φ) = ⟨1, mem_locKer_of_mem (one_mem R)⟩ from rfl, this,
      show (⟨(1 : ℂ), one_mem R⟩ : R) = 1 from rfl, map_one]
  map_mul' := by
    intro x y
    obtain ⟨s, hs, hs0, hsx⟩ := x.2
    obtain ⟨t, ht, ht0, hty⟩ := y.2
    have hst : s * t ∈ R := mul_mem hs ht
    have hst0 : φ ⟨s * t, hst⟩ ≠ 0 := by
      rw [map_mul_mk s t hs ht hst]; exact mul_ne_zero hs0 ht0
    have hmem : s * t * ((x * y : locKer R φ) : ℂ) ∈ R := by
      have : s * t * ((x : ℂ) * y) = (s * x) * (t * y) := by ring
      change s * t * ((x : ℂ) * y) ∈ R
      rw [this]; exact mul_mem hsx hty
    rw [locKerExt_eq _ hst hst0 hmem, locKerExt_eq x hs hs0 hsx, locKerExt_eq y ht ht0 hty]
    have hprod : (⟨s * t * ((x * y : locKer R φ) : ℂ), hmem⟩ : R) =
        ⟨s * x, hsx⟩ * ⟨t * y, hty⟩ := by
      apply Subtype.ext
      change s * t * ((x : ℂ) * y) = (s * x) * (t * y)
      ring
    rw [hprod, map_mul, map_mul_mk s t hs ht hst]
    field_simp
  map_zero' := by
    have := locKerExt_of_mem (φ := φ) (zero_mem R)
    rw [show (0 : locKer R φ) = ⟨0, mem_locKer_of_mem (zero_mem R)⟩ from rfl, this,
      show (⟨(0 : ℂ), zero_mem R⟩ : R) = 0 from rfl, map_zero]
  map_add' := by
    intro x y
    obtain ⟨s, hs, hs0, hsx⟩ := x.2
    obtain ⟨t, ht, ht0, hty⟩ := y.2
    have hst : s * t ∈ R := mul_mem hs ht
    have hst0 : φ ⟨s * t, hst⟩ ≠ 0 := by
      rw [map_mul_mk s t hs ht hst]; exact mul_ne_zero hs0 ht0
    have hmem : s * t * ((x + y : locKer R φ) : ℂ) ∈ R := by
      have : s * t * ((x : ℂ) + y) = t * (s * x) + s * (t * y) := by ring
      change s * t * ((x : ℂ) + y) ∈ R
      rw [this]
      exact add_mem (mul_mem ht hsx) (mul_mem hs hty)
    rw [locKerExt_eq _ hst hst0 hmem, locKerExt_eq x hs hs0 hsx, locKerExt_eq y ht ht0 hty]
    have hsum : (⟨s * t * ((x + y : locKer R φ) : ℂ), hmem⟩ : R) =
        ⟨t, ht⟩ * ⟨s * x, hsx⟩ + ⟨s, hs⟩ * ⟨t * y, hty⟩ := by
      apply Subtype.ext
      change s * t * ((x : ℂ) + y) = t * (s * x) + s * (t * y)
      ring
    rw [hsum, map_add, map_mul, map_mul, map_mul_mk s t hs ht hst]
    field_simp

theorem locKerHom_apply (z : locKer R φ) : locKerHom z = locKerExt z := rfl

theorem locKerHom_of_mem {z : ℂ} (hz : z ∈ R) :
    locKerHom (⟨z, mem_locKer_of_mem hz⟩ : locKer R φ) = φ ⟨z, hz⟩ :=
  locKerExt_of_mem hz

theorem mem_locKer_of_mul_mem {z s : ℂ} (hs : s ∈ R) (hs0 : φ ⟨s, hs⟩ ≠ 0) (hsz : s * z ∈ R) :
    z ∈ locKer R φ := ⟨s, hs, hs0, hsz⟩

theorem locKerHom_eq_of_mul_mem {z s : ℂ} (hs : s ∈ R) (hs0 : φ ⟨s, hs⟩ ≠ 0)
    (hsz : s * z ∈ R) :
    locKerHom (⟨z, mem_locKer_of_mul_mem hs hs0 hsz⟩ : locKer R φ) =
      φ ⟨s * z, hsz⟩ * (φ ⟨s, hs⟩)⁻¹ := by
  rw [locKerHom_apply, locKerExt_eq _ hs hs0 hsz]

end Loc

theorem exists_natCast_eq_of_pow_eq_self {F : Type} [CommRing F] [IsDomain F] {ℓ : ℕ}
    [hℓ : Fact ℓ.Prime] [CharP F ℓ] {x : F} (hx : x ^ ℓ = x) : ∃ i : ℕ, i < ℓ ∧ (i : F) = x := by
  classical
  by_contra hcon
  push Not at hcon
  have hℓp : ℓ.Prime := hℓ.out
  have hℓ2 : 2 ≤ ℓ := hℓp.two_le

  set P : F[X] := X ^ ℓ - X with hP
  have hPdeg : P.natDegree = ℓ := by
    rw [hP]
    have h1 : (X : F[X]).natDegree < (X ^ ℓ : F[X]).natDegree := by
      rw [natDegree_X_pow, natDegree_X]; omega
    rw [natDegree_sub_eq_left_of_natDegree_lt h1, natDegree_X_pow]
  have hP0 : P ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [hPdeg, natDegree_zero] at this
    omega
  have hroot_nat : ∀ i : ℕ, P.IsRoot (i : F) := by
    intro i
    rw [hP, IsRoot.def, eval_sub, eval_pow, eval_X]
    have : (ZMod.castHom (dvd_refl ℓ) F (i : ZMod ℓ)) ^ ℓ =
        ZMod.castHom (dvd_refl ℓ) F (i : ZMod ℓ) := by
      rw [← map_pow, ZMod.pow_card]
    rw [map_natCast] at this
    rw [this, sub_self]
  have hroot_x : P.IsRoot x := by
    rw [hP, IsRoot.def, eval_sub, eval_pow, eval_X, hx, sub_self]

  set Z : Finset F := insert x ((Finset.range ℓ).image (fun i : ℕ => (i : F))) with hZ
  have hcard_img : ((Finset.range ℓ).image (fun i : ℕ => (i : F))).card = ℓ := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hi' : i < ℓ := Finset.mem_range.1 hi
    have hj' : j < ℓ := Finset.mem_range.1 hj
    have hmod : i ≡ j [MOD ℓ] := (CharP.natCast_eq_natCast (R := F) (p := ℓ)).1 hij
    exact Nat.ModEq.eq_of_lt_of_lt hmod hi' hj'
  have hxnot : x ∉ (Finset.range ℓ).image (fun i : ℕ => (i : F)) := by
    intro hxm
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.1 hxm
    exact hcon i (Finset.mem_range.1 hi) hix
  have hcardZ : Z.card = ℓ + 1 := by
    rw [hZ, Finset.card_insert_of_notMem hxnot, hcard_img]
  have hsub : Z.val ⊆ P.roots := by
    intro z hz
    rw [Finset.mem_val] at hz
    rw [mem_roots hP0]
    rw [hZ, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact hroot_x
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hz
      exact hroot_nat i
  have := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hcardZ, hPdeg] at this
  omega

section Ext

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
  {κ : Type} [Field κ] [Finite κ] (φ : A →+* κ)
  {ℓ : ℕ} [Fact ℓ.Prime] [CharP κ ℓ] (b : B) (hb : b ^ (ℓ - 1) = 1)

include hb in

theorem exists_ringHom_extends_of_pow_eq_one
    (hinj : Function.Injective (algebraMap A B)) (hgen : ∀ x : B, x ∈ Algebra.adjoin A {b}) :
    ∃ ψ : B →+* κ, ∀ a : A, ψ (algebraMap A B a) = φ a := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hℓ1 : 1 ≤ ℓ := hℓ.one_lt.le

  have hbint : IsIntegral A b := by
    refine ⟨X ^ (ℓ - 1) - 1, ?_, ?_⟩
    · exact monic_X_pow_sub_C (1 : A) (by have := hℓ.two_le; omega)
    · simp [hb]
  haveI : Algebra.IsIntegral A B := by
    refine ⟨fun x => ?_⟩
    have hle : Algebra.adjoin A {b} ≤ integralClosure A B :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 ((mem_integralClosure_iff A B).2 hbint))
    exact (mem_integralClosure_iff A B).1 (hle (hgen x))

  set 𝔭 : Ideal A := RingHom.ker φ with h𝔭
  haveI h𝔭prime : 𝔭.IsPrime := RingHom.ker_isPrime φ
  haveI : IsDomain (A ⧸ 𝔭) := (Ideal.Quotient.isDomain_iff_prime 𝔭).2 h𝔭prime
  have hinjφ : Function.Injective (RingHom.kerLift φ) := RingHom.kerLift_injective φ
  haveI : Finite (A ⧸ 𝔭) := Finite.of_injective _ hinjφ
  haveI h𝔭max : 𝔭.IsMaximal :=
    Ideal.Quotient.maximal_of_isField 𝔭 (Finite.isField_of_domain (A ⧸ 𝔭))

  have hker : RingHom.ker (algebraMap A B) ≤ 𝔭 := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx0 : x = 0 := hinj (by rw [hx, map_zero])
    rw [hx0]; exact zero_mem 𝔭
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B) 𝔭 hker
  haveI : Q.IsMaximal := hQmax
  have hle : 𝔭 ≤ Q.comap (algebraMap A B) := le_of_eq hQ.symm
  set ι : A ⧸ 𝔭 →+* B ⧸ Q := Ideal.quotientMap Q (algebraMap A B) hle with hι

  have hℓQ : ((ℓ : B ⧸ Q)) = 0 := by
    have h1 : (ℓ : A) ∈ 𝔭 := by
      rw [h𝔭, RingHom.mem_ker, map_natCast]
      exact CharP.cast_eq_zero κ ℓ
    have h2 : (ℓ : A ⧸ 𝔭) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk 𝔭), Ideal.Quotient.eq_zero_iff_mem]
      exact h1
    have := congrArg ι h2
    rwa [map_natCast, map_zero] at this
  haveI : Nontrivial (B ⧸ Q) := Ideal.Quotient.nontrivial_iff.2 hQmax.ne_top
  haveI : CharP (B ⧸ Q) ℓ := by
    have := CharP.ringChar_of_prime_eq_zero hℓ hℓQ
    exact this ▸ ringChar.charP (B ⧸ Q)

  have hfix : (Ideal.Quotient.mk Q b) ^ ℓ = Ideal.Quotient.mk Q b := by
    have : (Ideal.Quotient.mk Q b) ^ (ℓ - 1) = 1 := by
      rw [← map_pow, hb, map_one]
    calc (Ideal.Quotient.mk Q b) ^ ℓ
        = (Ideal.Quotient.mk Q b) ^ (ℓ - 1) * Ideal.Quotient.mk Q b := by
          rw [← pow_succ, Nat.sub_add_cancel hℓ1]
      _ = Ideal.Quotient.mk Q b := by rw [this, one_mul]
  obtain ⟨i₀, -, hi₀⟩ := exists_natCast_eq_of_pow_eq_self hfix

  have hsurj : Function.Surjective ι := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hs := hgen s
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨(i₀ : A ⧸ 𝔭), ?_⟩
      rw [map_natCast, hi₀]
    | algebraMap r =>
      refine ⟨Ideal.Quotient.mk 𝔭 r, ?_⟩
      rw [hι, Ideal.quotientMap_mk]
    | add x y hx hy ihx ihy =>
      obtain ⟨c, hc⟩ := ihx
      obtain ⟨d, hd⟩ := ihy
      exact ⟨c + d, by rw [map_add, hc, hd, ← map_add]⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨c, hc⟩ := ihx
      obtain ⟨d, hd⟩ := ihy
      exact ⟨c * d, by rw [map_mul, hc, hd, ← map_mul]⟩
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hι, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hQ, Ideal.mem_comap]
    exact hx
  have hbij : Function.Bijective ι := ⟨hιinj, hsurj⟩
  set e : A ⧸ 𝔭 ≃+* B ⧸ Q := RingEquiv.ofBijective ι hbij with he

  set φbar : A ⧸ 𝔭 →+* κ := Ideal.Quotient.lift 𝔭 φ (fun r hr => hr) with hφbar
  refine ⟨(φbar.comp e.symm.toRingHom).comp (Ideal.Quotient.mk Q), fun a => ?_⟩
  rw [RingHom.comp_apply, RingHom.comp_apply]
  have h2 : Ideal.Quotient.mk Q (algebraMap A B a) = e (Ideal.Quotient.mk 𝔭 a) := by
    rw [he, RingEquiv.ofBijective_apply, hι, Ideal.quotientMap_mk]
  rw [h2]
  change φbar (e.symm (e (Ideal.Quotient.mk 𝔭 a))) = φ a
  rw [RingEquiv.symm_apply_apply, hφbar, Ideal.Quotient.lift_mk]

end Ext

section ExtC

variable (R : Subalgebra ℤ ℂ) {κ : Type} [Field κ] [Finite κ] (φ : R →+* κ)
  {ℓ : ℕ} [Fact ℓ.Prime] [CharP κ ℓ] (ζ : ℂ) (hζ : ζ ^ (ℓ - 1) = 1)

def adjoinRoot' : Subalgebra ℤ ℂ := Algebra.adjoin ℤ (insert ζ (R : Set ℂ))

theorem le_adjoinRoot' : R ≤ adjoinRoot' R ζ := fun _ hz =>
  Algebra.subset_adjoin (Set.mem_insert_of_mem ζ hz)

theorem self_mem_adjoinRoot' : ζ ∈ adjoinRoot' R ζ :=
  Algebra.subset_adjoin (Set.mem_insert ζ _)

include hζ in

theorem exists_ringHom_adjoinRoot'_extends :
    ∃ φ₁ : adjoinRoot' R ζ →+* κ,
      ∀ (z : ℂ) (hz : z ∈ R), φ₁ ⟨z, le_adjoinRoot' R ζ hz⟩ = φ ⟨z, hz⟩ := by
  classical
  set R₁ := adjoinRoot' R ζ with hR₁
  let incl : R →ₐ[ℤ] R₁ := Subalgebra.inclusion (le_adjoinRoot' R ζ)
  letI : Algebra R R₁ := incl.toRingHom.toAlgebra
  have halg : ∀ r : R, algebraMap R R₁ r = incl r := fun _ => rfl
  have hinj : Function.Injective (algebraMap R R₁) := Subalgebra.inclusion_injective _
  set b : R₁ := ⟨ζ, self_mem_adjoinRoot' R ζ⟩ with hbdef
  have hb : b ^ (ℓ - 1) = 1 := Subtype.ext (by simp [hbdef, hζ])
  have hgen : ∀ x : R₁, x ∈ Algebra.adjoin R {b} := by
    rintro ⟨x, hx⟩
    induction hx using Algebra.adjoin_induction with
    | mem z hz =>
      rcases Set.mem_insert_iff.1 hz with rfl | hzR
      · exact Algebra.subset_adjoin (Set.mem_singleton _)
      · have : (⟨z, Algebra.subset_adjoin hz⟩ : R₁) = algebraMap R R₁ ⟨z, hzR⟩ :=
          Subtype.ext rfl
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
    | algebraMap n =>
      have : (⟨algebraMap ℤ ℂ n, Subalgebra.algebraMap_mem _ n⟩ : R₁) = (n : R₁) :=
        Subtype.ext (by simp)
      rw [this]
      exact intCast_mem _ n
    | add z w hz hw ihz ihw => exact add_mem ihz ihw
    | mul z w hz hw ihz ihw => exact mul_mem ihz ihw
  obtain ⟨ψ, hψ⟩ := exists_ringHom_extends_of_pow_eq_one φ b hb hinj hgen
  refine ⟨ψ, fun z hz => ?_⟩
  have : (⟨z, le_adjoinRoot' R ζ hz⟩ : R₁) = algebraMap R R₁ ⟨z, hz⟩ := Subtype.ext rfl
  rw [this, hψ]

end ExtC

theorem isPrimitiveRoot_map_of_isPrimitiveRoot {R₁ : Subalgebra ℤ ℂ} {κ : Type} [Field κ]
    (φ₁ : R₁ →+* κ) {n : ℕ} [NeZero (n : κ)] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hζR : ζ ∈ R₁) :
    IsPrimitiveRoot (φ₁ ⟨ζ, hζR⟩) n := by
  have hn0 : n ≠ 0 := by
    intro h
    have : ((n : ℕ) : κ) = 0 := by rw [h, Nat.cast_zero]
    exact NeZero.ne (n : κ) this
  haveI : NeZero (n : ℂ) := ⟨by exact_mod_cast hn0⟩

  have hrootC : (cyclotomic n ℂ).IsRoot ζ := (isRoot_cyclotomic_iff).2 hζ
  set ζ' : R₁ := ⟨ζ, hζR⟩ with hζ'
  have haevalC : aeval ζ (cyclotomic n ℤ) = 0 := by
    rw [aeval_def, algebraMap_int_eq, ← eval_map, map_cyclotomic_int]
    exact hrootC
  have haeval' : aeval ζ' (cyclotomic n ℤ) = 0 := by
    have h := aeval_algHom_apply (R₁.val.toRingHom.toIntAlgHom) ζ' (cyclotomic n ℤ)
    have hval : (R₁.val.toRingHom.toIntAlgHom) ζ' = ζ := rfl
    rw [hval, haevalC] at h

    apply Subtype.ext
    change ((aeval ζ' (cyclotomic n ℤ) : R₁) : ℂ) = 0
    exact h.symm
  have haevalκ : aeval (φ₁ ζ') (cyclotomic n ℤ) = 0 := by
    have h := aeval_algHom_apply φ₁.toIntAlgHom ζ' (cyclotomic n ℤ)
    change aeval (φ₁ ζ') (cyclotomic n ℤ) = φ₁ (aeval ζ' (cyclotomic n ℤ)) at h
    rw [h, haeval', map_zero]
  have hrootκ : (cyclotomic n κ).IsRoot (φ₁ ζ') := by
    rw [IsRoot.def, ← map_cyclotomic_int, eval_map, ← algebraMap_int_eq, ← aeval_def]
    exact haevalκ
  exact (isRoot_cyclotomic_iff).1 hrootκ

section Teich

variable {R₁ : Subalgebra ℤ ℂ} {κ : Type} [Field κ] (φ₁ : R₁ →+* κ)
  {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP κ ℓ]
  {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (ℓ - 1)) (hζR : ζ ∈ R₁)
  (hμ : IsPrimitiveRoot (φ₁ ⟨ζ, hζR⟩) (ℓ - 1))

def ubar (ℓ : ℕ) (κ : Type) [Field κ] [CharP κ ℓ] (u : (ZMod ℓ)ˣ) : κ :=
  ZMod.castHom (dvd_refl ℓ) κ (u : ZMod ℓ)

theorem ubar_ne_zero (u : (ZMod ℓ)ˣ) : ubar ℓ κ u ≠ 0 := by
  unfold ubar
  intro h
  have : ((u : ZMod ℓ)) = 0 := by
    have hinj : Function.Injective (ZMod.castHom (dvd_refl ℓ) κ) :=
      (ZMod.castHom (dvd_refl ℓ) κ).injective
    exact hinj (by rw [h, map_zero])
  exact u.ne_zero this

theorem ubar_mul (u v : (ZMod ℓ)ˣ) : ubar ℓ κ (u * v) = ubar ℓ κ u * ubar ℓ κ v := by
  unfold ubar
  rw [Units.val_mul, map_mul]

theorem ubar_inv (u : (ZMod ℓ)ˣ) : (ubar ℓ κ u)⁻¹ = ubar ℓ κ u⁻¹ := by
  symm
  apply eq_inv_of_mul_eq_one_right
  rw [← ubar_mul, mul_inv_cancel]
  simp [ubar]

theorem ubar_inv_pow (u : (ZMod ℓ)ˣ) : (ubar ℓ κ u)⁻¹ ^ (ℓ - 1) = 1 := by
  rw [ubar_inv]
  unfold ubar
  have h : ((u⁻¹ : (ZMod ℓ)ˣ) : ZMod ℓ) ^ (ℓ - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one (Units.ne_zero _)
  have := congrArg (ZMod.castHom (dvd_refl ℓ) κ) h
  rwa [map_pow, map_one] at this

include hμ in
theorem exists_pow_eq_ubar_inv (u : (ZMod ℓ)ˣ) :
    ∃ j : ℕ, (φ₁ ⟨ζ, hζR⟩) ^ j = (ubar ℓ κ u)⁻¹ := by
  haveI : NeZero (ℓ - 1) := ⟨by have := hℓ.out.two_le; omega⟩
  obtain ⟨j, -, hj⟩ := hμ.eq_pow_of_pow_eq_one (ubar_inv_pow u)
  exact ⟨j, hj⟩

noncomputable def teichExp (u : (ZMod ℓ)ˣ) : ℕ := (exists_pow_eq_ubar_inv φ₁ hζR hμ u).choose

theorem teichExp_spec (u : (ZMod ℓ)ˣ) :
    (φ₁ ⟨ζ, hζR⟩) ^ teichExp φ₁ hζR hμ u = (ubar ℓ κ u)⁻¹ :=
  (exists_pow_eq_ubar_inv φ₁ hζR hμ u).choose_spec

private theorem _root_.IsPrimitiveRoot.pow_eq_pow_iff_modEq' {M : Type} [CommMonoid M] {x : M} {k : ℕ}
    (h : IsPrimitiveRoot x k) (hk : k ≠ 0) (a b : ℕ) : x ^ a = x ^ b ↔ a ≡ b [MOD k] := by
  have hfin : IsOfFinOrder x :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨k, Nat.pos_of_ne_zero hk, h.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← h.eq_orderOf]

p2m_alias "P2MW.S_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen.IsPrimitiveRoot.pow_eq_pow_iff_modEq'" "IsPrimitiveRoot.pow_eq_pow_iff_modEq'"
include hζ hμ in
omit [CharP κ ℓ] in

theorem pow_eq_pow_iff (a b : ℕ) :
    (φ₁ ⟨ζ, hζR⟩) ^ a = (φ₁ ⟨ζ, hζR⟩) ^ b ↔ ζ ^ a = ζ ^ b := by
  have hk : ℓ - 1 ≠ 0 := by have := hℓ.out.two_le; omega
  rw [hμ.pow_eq_pow_iff_modEq' hk, hζ.pow_eq_pow_iff_modEq' hk]

noncomputable def zetaUnit : ℂˣ := Units.mk0 ζ (hζ.ne_zero (by have := hℓ.out.two_le; omega))

@[scoped simp] theorem val_zetaUnit : (zetaUnit hζ : ℂ) = ζ := rfl

noncomputable def teichUnitHom : (ZMod ℓ)ˣ →* ℂˣ where
  toFun u := zetaUnit hζ ^ teichExp φ₁ hζR hμ u
  map_one' := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, val_zetaUnit, Units.val_one]
    have h := teichExp_spec φ₁ hζR hμ 1
    have h1 : (ubar ℓ κ 1)⁻¹ = 1 := by simp [ubar]
    rw [h1, ← pow_zero (φ₁ ⟨ζ, hζR⟩), pow_eq_pow_iff φ₁ hζ hζR hμ] at h
    rw [h, pow_zero]
  map_mul' u v := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, val_zetaUnit, ← pow_add]
    rw [← pow_eq_pow_iff φ₁ hζ hζR hμ, pow_add, teichExp_spec, teichExp_spec, teichExp_spec,
      ubar_mul, mul_inv]

noncomputable def teich : DirichletCharacter ℂ ℓ := MulChar.ofUnitHom (teichUnitHom φ₁ hζ hζR hμ)

theorem teich_apply_unit (u : (ZMod ℓ)ˣ) :
    teich φ₁ hζ hζR hμ (u : ZMod ℓ) = ζ ^ teichExp φ₁ hζR hμ u := by
  rw [teich, MulChar.ofUnitHom_coe]
  change ((zetaUnit hζ ^ teichExp φ₁ hζR hμ u : ℂˣ) : ℂ) = _
  rw [Units.val_pow_eq_pow_val, val_zetaUnit]

theorem teich_mem (x : ZMod ℓ) : teich φ₁ hζ hζR hμ x ∈ R₁ := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    rw [teich_apply_unit]
    exact pow_mem hζR _
  · rw [MulChar.map_nonunit _ hx]
    exact zero_mem R₁

theorem map_teich_mul_ubar (u : (ZMod ℓ)ˣ) :
    φ₁ ⟨teich φ₁ hζ hζR hμ (u : ZMod ℓ), teich_mem φ₁ hζ hζR hμ _⟩ * ubar ℓ κ u = 1 := by
  have h : (⟨teich φ₁ hζ hζR hμ (u : ZMod ℓ), teich_mem φ₁ hζ hζR hμ _⟩ : R₁) =
      ⟨ζ, hζR⟩ ^ teichExp φ₁ hζR hμ u := by
    apply Subtype.ext
    change teich φ₁ hζ hζR hμ (u : ZMod ℓ) = ((⟨ζ, hζR⟩ ^ teichExp φ₁ hζR hμ u : R₁) : ℂ)
    rw [Subalgebra.coe_pow]
    exact teich_apply_unit φ₁ hζ hζR hμ u
  rw [h, map_pow, teichExp_spec, inv_mul_cancel₀ (ubar_ne_zero u)]

theorem map_teich_natCast_mul {p : ℕ} (hpℓ : ¬ ℓ ∣ p) :
    φ₁ ⟨teich φ₁ hζ hζR hμ (p : ZMod ℓ), teich_mem φ₁ hζ hζR hμ _⟩ * (p : κ) = 1 := by
  have hcop : p.Coprime ℓ := (Nat.Prime.coprime_iff_not_dvd hℓ.out).2 hpℓ |>.symm
  have hu : ((ZMod.unitOfCoprime p hcop : (ZMod ℓ)ˣ) : ZMod ℓ) = (p : ZMod ℓ) :=
    ZMod.coe_unitOfCoprime p hcop
  have h := map_teich_mul_ubar φ₁ hζ hζR hμ (ZMod.unitOfCoprime p hcop)
  have hub : ubar ℓ κ (ZMod.unitOfCoprime p hcop) = (p : κ) := by
    unfold ubar
    rw [hu, map_natCast]
  rw [hub] at h
  have hel : (⟨teich φ₁ hζ hζR hμ (p : ZMod ℓ), teich_mem φ₁ hζ hζR hμ _⟩ : R₁) =
      ⟨teich φ₁ hζ hζR hμ ((ZMod.unitOfCoprime p hcop : (ZMod ℓ)ˣ) : ZMod ℓ),
        teich_mem φ₁ hζ hζR hμ _⟩ := by
    apply Subtype.ext
    change teich φ₁ hζ hζR hμ (p : ZMod ℓ) = teich φ₁ hζ hζR hμ _
    rw [hu]
  rw [hel]
  exact h

include hℓ in

theorem pow_half_eq_neg_one {K : Type} [CommRing K] [IsDomain K] {x : K}
    (hx : IsPrimitiveRoot x (ℓ - 1)) (hℓ2 : ℓ ≠ 2) : x ^ ((ℓ - 1) / 2) = -1 := by
  have hℓp := hℓ.out
  have hodd : ℓ % 2 = 1 := Nat.odd_iff.1 (hℓp.odd_of_ne_two hℓ2)
  have heven : ℓ - 1 = (ℓ - 1) / 2 * 2 := by omega
  have hpos : 0 < ℓ - 1 := by have := hℓp.two_le; omega
  have h2 : IsPrimitiveRoot (x ^ ((ℓ - 1) / 2)) 2 := hx.pow hpos heven
  exact h2.eq_neg_one_of_two_right

theorem teich_odd (hℓ2 : ℓ ≠ 2) : (teich φ₁ hζ hζR hμ).Odd := by
  rw [DirichletCharacter.Odd]
  have hu : ((-1 : (ZMod ℓ)ˣ) : ZMod ℓ) = -1 := by rw [Units.val_neg, Units.val_one]
  rw [← hu, teich_apply_unit]

  have h1 := teichExp_spec φ₁ hζR hμ (-1)
  have hneg : (ubar ℓ κ (-1))⁻¹ = -1 := by
    unfold ubar
    rw [Units.val_neg, Units.val_one, map_neg, map_one, inv_neg, inv_one]
  rw [hneg, ← pow_half_eq_neg_one hμ hℓ2, pow_eq_pow_iff φ₁ hζ hζR hμ] at h1
  rw [h1, pow_half_eq_neg_one hζ hℓ2]

theorem teich_isPrimitive (hℓ2 : ℓ ≠ 2) : (teich φ₁ hζ hζR hμ).IsPrimitive := by
  have hℓp := hℓ.out
  haveI : NeZero ℓ := ⟨hℓp.ne_zero⟩
  rw [DirichletCharacter.isPrimitive_def]
  have hne : teich φ₁ hζ hζR hμ ≠ 1 := by
    intro h
    have hodd := teich_odd φ₁ hζ hζR hμ hℓ2
    rw [DirichletCharacter.Odd, h, MulChar.one_apply (isUnit_one.neg)] at hodd

    norm_num at hodd
  have hc1 : (teich φ₁ hζ hζR hμ).conductor ≠ 1 := by
    intro h
    exact hne (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h)
  have hdvd := DirichletCharacter.conductor_dvd_level (teich φ₁ hζ hζR hμ)
  rcases (Nat.dvd_prime hℓp).1 hdvd with h | h
  · exact absurd h hc1
  · exact h

theorem teichSum_mem :
    (∑ a ∈ Finset.range ℓ, (a : ℂ) * teich φ₁ hζ hζR hμ (a : ZMod ℓ)) ∈ R₁ :=
  Subalgebra.sum_mem R₁ fun a _ => mul_mem (natCast_mem R₁ a) (teich_mem φ₁ hζ hζR hμ _)

theorem map_sum_eq_neg_one :
    φ₁ ⟨∑ a ∈ Finset.range ℓ, (a : ℂ) * teich φ₁ hζ hζR hμ (a : ZMod ℓ),
        teichSum_mem φ₁ hζ hζR hμ⟩ = -1 := by
  have hℓp := hℓ.out

  have hsum : (⟨∑ a ∈ Finset.range ℓ, (a : ℂ) * teich φ₁ hζ hζR hμ (a : ZMod ℓ),
      teichSum_mem φ₁ hζ hζR hμ⟩ : R₁) =
      ∑ a ∈ Finset.range ℓ, (a : R₁) * ⟨teich φ₁ hζ hζR hμ (a : ZMod ℓ), teich_mem φ₁ hζ hζR hμ _⟩ := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul]
    rfl
  rw [hsum, map_sum]

  have hterm : ∀ a ∈ Finset.range ℓ,
      φ₁ ((a : R₁) * ⟨teich φ₁ hζ hζR hμ (a : ZMod ℓ), teich_mem φ₁ hζ hζR hμ _⟩) =
        if a = 0 then (0 : κ) else 1 := by
    intro a ha
    rw [map_mul, map_natCast]
    split_ifs with h0
    · rw [h0, Nat.cast_zero, zero_mul]
    · have ha' : a < ℓ := Finset.mem_range.1 ha
      have hℓa : ¬ ℓ ∣ a := fun h => by
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h
        omega
      rw [mul_comm]
      exact map_teich_natCast_mul φ₁ hζ hζR hμ hℓa
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : ((Finset.range ℓ).filter (fun a => ¬ a = 0)).card = ℓ - 1 := by
    have : (Finset.range ℓ).filter (fun a => ¬ a = 0) = (Finset.range ℓ).erase 0 := by
      ext a
      simp [Finset.mem_filter, Finset.mem_erase, and_comm]
    rw [this, Finset.card_erase_of_mem (Finset.mem_range.2 hℓp.pos), Finset.card_range]
  rw [hcard, Nat.cast_sub hℓp.one_lt.le, Nat.cast_one, CharP.cast_eq_zero κ ℓ, zero_sub]

end Teich

section Engine

variable {N : ℕ} [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
  (hf₁ : qCoeff f 1 = 1)
  (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
      qCoeff f (p * n) + ε (p : ZMod N) * (if p ∣ n then qCoeff f (n / p) else 0) =
        qCoeff f p * qCoeff f n)
  (R : Subalgebra ℤ ℂ) (hR : ∀ n : ℕ, qCoeff f n ∈ R) (hε : ∀ x : ZMod N, ε x ∈ R)
  (κ : Type) [Field κ] [Finite κ] (φ : R →+* κ)
  {L : ℕ} [NeZero L] (hL : ∀ p : ℕ, p.Prime → (p ∣ L ↔ (p : κ) = 0))
  (χ : DirichletCharacter ℂ L) (E : ModularForm (Gamma1 L) 1)
  (hEχ : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 L → ∀ τ : ℍ,
      E (γ • τ) =
        χ ((γ 1 1 : ℤ) : ZMod L) *
          ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (1 : ℤ) * E τ))
  (R₁ : Subalgebra ℤ ℂ) (hRR₁ : R ≤ R₁) (φ₁ : R₁ →+* κ)
  (hφ₁ : ∀ (z : ℂ) (hz : z ∈ R), φ₁ ⟨z, hRR₁ hz⟩ = φ ⟨z, hz⟩)
  (hχR₁ : ∀ x : ZMod L, χ x ∈ R₁)
  (hχp : ∀ p : ℕ, p.Prime → ¬ p ∣ L → φ₁ ⟨χ (p : ZMod L), hχR₁ _⟩ * (p : κ) = 1)
  (hEm : ∀ m : ℕ, 0 < m → qCoeff E m ∈ R₁)
  (hE0 : qCoeff E 0 ≠ 0)
  (s : ℂ) (hs : s ∈ R₁) (hs0 : φ₁ ⟨s, hs⟩ ≠ 0)
  (hsc : s * (qCoeff E 0)⁻¹ ∈ R₁) (hsc0 : φ₁ ⟨s * (qCoeff E 0)⁻¹, hsc⟩ = 0)

include hf₁ hT hL hEχ hφ₁ hχp hEm hE0 hs0 hsc0 in
theorem engine :
    ∃ (M : ℕ) (_ : NeZero M),
      (∀ p : ℕ, p.Prime → (p ∣ M ↔ p ∣ N ∨ (p : κ) = 0)) ∧
      ∃ (η : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) 2) (b : ℕ → ℂ),
        g ≠ 0 ∧ CuspForm.HasNebentypus η g ∧
        (∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
          qCoeff g (p * n) + η (p : ZMod M) * (p : ℂ) * (if p ∣ n then qCoeff g (n / p) else 0) =
            b p * qCoeff g n) ∧
        ∃ (R' : Subalgebra ℤ ℂ) (φ' : R' →+* κ) (hη : ∀ x : ZMod M, η x ∈ R')
          (hb : ∀ p : ℕ, p.Prime → ¬ p ∣ M → b p ∈ R'),
          ∀ (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M),
            φ' ⟨b p, hb p hp hpM⟩ = φ ⟨qCoeff f p, hR p⟩ ∧
            φ' ⟨η (p : ZMod M), hη _⟩ * (p : κ) = φ ⟨ε (p : ZMod N), hε _⟩ := by
  classical

  set M : ℕ := N * L with hM
  haveI : NeZero M := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne L)⟩
  have hNM : N ∣ M := Dvd.intro L rfl
  have hLM : L ∣ M := Dvd.intro_left N rfl
  have hMprimes : ∀ p : ℕ, p.Prime → (p ∣ M ↔ p ∣ N ∨ (p : κ) = 0) := by
    intro p hp
    rw [hM, Nat.Prime.dvd_mul hp, hL p hp]
  have hpκ : ∀ p : ℕ, p.Prime → ¬ p ∣ M → (p : κ) ≠ 0 := fun p hp hpM h =>
    hpM ((hMprimes p hp).2 (Or.inr h))
  have hpN : ∀ p : ℕ, ¬ p ∣ M → ¬ p ∣ N := fun p hpM h => hpM (dvd_trans h hNM)
  have hpL : ∀ p : ℕ, ¬ p ∣ M → ¬ p ∣ L := fun p hpM h => hpM (dvd_trans h hLM)

  set c : ℂ := (qCoeff E 0)⁻¹ with hc
  set fM : CuspForm (Gamma1 M) 1 := restrictCF hNM f with hfM
  set EM : ModularForm (Gamma1 M) 1 := restrictMF hLM E with hEM
  set E' : ModularForm (Gamma1 M) 1 := c • EM with hE'
  have hE'coe : ⇑E' = c • ⇑E := rfl
  set h₀ : CuspForm (Gamma1 M) (1 + 1) := fM.mulModularForm E' with hh₀
  have h12 : (1 : ℤ) + 1 = ((2 : ℕ) : ℤ) := by norm_num
  set h : CuspForm (Gamma1 M) ((2 : ℕ) : ℤ) := CuspForm.mcast h12 h₀ with hh
  have hcoe : ⇑h = ⇑f * (c • ⇑E) := by
    change ⇑h₀ = _
    rw [hh₀, CuspForm.coe_mulModularForm]
    rfl

  set εM : DirichletCharacter ℂ M := DirichletCharacter.changeLevel hNM ε with hεM
  set χM : DirichletCharacter ℂ M := DirichletCharacter.changeLevel hLM χ with hχM
  set η : DirichletCharacter ℂ M := εM * χM with hη

  have hfε : CuspForm.HasNebentypus ε f := hasNebentypus_of_hecke ε f hT
  have hηh : CuspForm.HasNebentypus η h := by
    intro γ hγ τ
    have hγN : γ ∈ Gamma0 N := gamma0_le_of_dvd hNM hγ
    have hγL : γ ∈ Gamma0 L := gamma0_le_of_dvd hLM hγ
    have h1 := hfε γ hγN τ
    have h2 := hEχ γ hγL τ
    rw [hcoe]
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1, h2, hη, MulChar.mul_apply, hεM, hχM, changeLevel_apply_entry hNM ε hγ,
      changeLevel_apply_entry hLM χ hγ, zpow_one, show (((2 : ℕ) : ℤ)) = 2 from rfl, zpow_two]
    ring

  set R₂ : Subalgebra ℤ ℂ := locKer R₁ φ₁ with hR₂
  set φ₂ : R₂ →+* κ := locKerHom with hφ₂
  have hR₁R₂ : ∀ {z : ℂ}, z ∈ R₁ → z ∈ R₂ := fun hz => mem_locKer_of_mem hz
  have hRR₂ : ∀ {z : ℂ}, z ∈ R → z ∈ R₂ := fun hz => hR₁R₂ (hRR₁ hz)
  have hφ₂R₁ : ∀ {z : ℂ} (hz : z ∈ R₁), φ₂ ⟨z, hR₁R₂ hz⟩ = φ₁ ⟨z, hz⟩ :=
    fun hz => locKerHom_of_mem hz
  have hφ₂R : ∀ {z : ℂ} (hz : z ∈ R), φ₂ ⟨z, hRR₂ hz⟩ = φ ⟨z, hz⟩ := by
    intro z hz
    rw [hφ₂R₁ (hRR₁ hz), hφ₁ z hz]

  have hc_mem : c ∈ R₂ := mem_locKer_of_mul_mem hs hs0 hsc
  have hc_red : φ₂ ⟨c, hc_mem⟩ = 0 := by
    have := locKerHom_eq_of_mul_mem (φ := φ₁) hs hs0 hsc
    rw [hφ₂]
    rw [this, hsc0, zero_mul]

  set e : ℕ → ℂ := fun m => c * qCoeff E m with he_def
  have hper := one_mem_strictPeriods_gamma1 M
  have he : ∀ m : ℕ, qCoeff (⇑E') m = e m := by
    intro m
    have h1 : qExpansion 1 (c • ⇑EM) = c • qExpansion 1 ⇑EM :=
      ModularForm.qExpansion_smul one_pos hper c EM
    change (qExpansion 1 (c • ⇑EM)).coeff m = c * (qExpansion 1 (⇑E)).coeff m
    rw [h1, map_smul, smul_eq_mul]
    rfl
  have he0 : e 0 = 1 := by
    rw [he_def]; exact inv_mul_cancel₀ hE0
  have he_mem : ∀ m : ℕ, e m ∈ R₂ := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [he0]; exact one_mem R₂
    · exact mul_mem hc_mem (hR₁R₂ (hEm m hm))
  have he_red : ∀ m : ℕ, 0 < m → φ₂ ⟨e m, he_mem m⟩ = 0 := by
    intro m hm
    have : (⟨e m, he_mem m⟩ : R₂) = ⟨c, hc_mem⟩ * ⟨qCoeff E m, hR₁R₂ (hEm m hm)⟩ := rfl
    rw [this, map_mul, hc_red, zero_mul]
  have he_red0 : φ₂ ⟨e 0, he_mem 0⟩ = 1 := by
    have h1 : (⟨e 0, he_mem 0⟩ : R₂) = 1 := Subtype.ext he0
    rw [h1, map_one]

  have hqexp : ∀ n : ℕ, qCoeff h n = ∑ m ∈ Finset.range (n + 1), e m * qCoeff f (n - m) := by
    intro n
    have hcoe' : ⇑h = ⇑E' * ⇑fM := by rw [hcoe, hE'coe, hfM, coe_restrictCF, mul_comm]
    have hfA : AnalyticAt ℂ (cuspFunction 1 (⇑fM)) 0 :=
      ModularFormClass.analyticAt_cuspFunction_zero fM one_pos hper
    have hEA : AnalyticAt ℂ (cuspFunction 1 (⇑E')) 0 :=
      ModularFormClass.analyticAt_cuspFunction_zero E' one_pos hper
    change (qExpansion 1 (⇑h)).coeff n = ∑ m ∈ Finset.range (n + 1), e m * (qExpansion 1 (⇑f)).coeff (n - m)
    rw [hcoe', qExpansion_mul hEA hfA, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← he m]
    rfl

  have hRh : ∀ n : ℕ, qCoeff h n ∈ R₂ := by
    intro n
    rw [hqexp n]
    exact Subalgebra.sum_mem R₂ fun m _ => mul_mem (he_mem m) (hRR₂ (hR _))
  have hred : ∀ n : ℕ, φ₂ ⟨qCoeff h n, hRh n⟩ = φ ⟨qCoeff f n, hR n⟩ := by
    intro n
    have hsum : (⟨qCoeff h n, hRh n⟩ : R₂) =
        ∑ m ∈ Finset.range (n + 1), (⟨e m, he_mem m⟩ : R₂) * ⟨qCoeff f (n - m), hRR₂ (hR _)⟩ := by
      apply Subtype.ext
      change qCoeff h n = ((∑ m ∈ Finset.range (n + 1),
        ((⟨e m, he_mem m⟩ : R₂) * ⟨qCoeff f (n - m), hRR₂ (hR _)⟩ : R₂) : R₂) : ℂ)
      rw [hqexp n]
      simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul]
    rw [hsum, map_sum, Finset.sum_range_succ']
    simp only [map_mul]
    rw [Finset.sum_eq_zero (fun m _ => by rw [he_red (m + 1) (Nat.succ_pos m), zero_mul]),
      zero_add, he_red0, one_mul, Nat.sub_zero, hφ₂R]
  have hne : ∃ n : ℕ, φ₂ ⟨qCoeff h n, hRh n⟩ ≠ 0 := by
    refine ⟨1, ?_⟩
    rw [hred 1]
    have : (⟨qCoeff f 1, hR 1⟩ : R) = 1 := Subtype.ext hf₁
    rw [this, map_one]
    exact one_ne_zero

  have hεMR : ∀ x : ZMod M, εM x ∈ R := fun x => changeLevel_mem' hNM ε R hε x
  have hχMR : ∀ x : ZMod M, χM x ∈ R₁ := fun x => changeLevel_mem' hLM χ R₁ hχR₁ x
  have hηR₂ : ∀ x : ZMod M, η x ∈ R₂ := by
    intro x
    rw [hη, MulChar.mul_apply]
    exact mul_mem (hRR₂ (hεMR x)) (hR₁R₂ (hχMR x))
  have hηp : ∀ p : ℕ, p.Prime → ¬ p ∣ M →
      φ₂ ⟨η (p : ZMod M), hηR₂ _⟩ * (p : κ) = φ ⟨ε (p : ZMod N), hε _⟩ := by
    intro p hp hpM
    have h1 : (⟨η (p : ZMod M), hηR₂ _⟩ : R₂) =
        ⟨ε (p : ZMod N), hRR₂ (hε _)⟩ * ⟨χ (p : ZMod L), hR₁R₂ (hχR₁ _)⟩ := by
      apply Subtype.ext
      change η (p : ZMod M) = ε (p : ZMod N) * χ (p : ZMod L)
      rw [hη, MulChar.mul_apply, hεM, hχM, changeLevel_natCast_of_not_dvd' hNM ε hp hpM,
        changeLevel_natCast_of_not_dvd' hLM χ hp hpM]
    rw [h1, map_mul, hφ₂R (hε _), hφ₂R₁ (hχR₁ _), mul_assoc, hχp p hp (hpL p hpM), mul_one]

  set α : ℕ → R₂ := fun p => ⟨qCoeff f p, hRR₂ (hR p)⟩ with hα
  have hTres : ∀ p : ℕ, p.Prime → ¬ p ∣ M → (p : κ) ≠ 0 → ∀ n : ℕ, ∃ r : R₂,
      (r : ℂ) = qCoeff h (p * n) +
          η (p : ZMod M) * (p : ℂ) ^ (2 - 1) *
            (if p ∣ n then qCoeff h (n / p) else 0) ∧
      φ₂ r = φ₂ (α p) * φ₂ ⟨qCoeff h n, hRh n⟩ := by
    intro p hp hpM hpk n
    have hite : (if p ∣ n then qCoeff h (n / p) else 0) ∈ R₂ := by
      split_ifs
      · exact hRh _
      · exact zero_mem R₂
    let r : R₂ := ⟨qCoeff h (p * n), hRh _⟩ + ⟨η (p : ZMod M), hηR₂ _⟩ * (p : R₂) ^ (2 - 1) * ⟨_, hite⟩
    refine ⟨r, ?_, ?_⟩
    · simp [r]
    · have hite_red : φ₂ ⟨_, hite⟩ = (if p ∣ n then φ ⟨qCoeff f (n / p), hR _⟩ else 0) := by
        split_ifs with hpn
        · exact hred (n / p)
        · exact map_zero φ₂
      have hηp' := hηp p hp hpM
      simp only [r, map_add, map_mul, map_pow, map_natCast, hred, hite_red]
      rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one, hηp']
      rw [show φ₂ (α p) = φ ⟨qCoeff f p, hR p⟩ from hφ₂R (hR p)]

      have key : (⟨qCoeff f (p * n), hR _⟩ : R) +
          ⟨ε (p : ZMod N), hε _⟩ * (if p ∣ n then ⟨qCoeff f (n / p), hR _⟩ else 0) =
          ⟨qCoeff f p, hR p⟩ * ⟨qCoeff f n, hR n⟩ := by
        apply Subtype.ext
        have := hT p hp (hpN p hpM) n
        split_ifs with hpn
        · simp only [Subalgebra.coe_add, Subalgebra.coe_mul]
          rwa [if_pos hpn] at this
        · simp only [Subalgebra.coe_add, Subalgebra.coe_mul, mul_zero, ZeroMemClass.coe_zero]
          rw [if_neg hpn, mul_zero] at this
          exact this
      have := congrArg φ key
      simp only [map_add, map_mul] at this
      rw [← this]
      congr 1
      split_ifs <;> simp

  obtain ⟨g, b, hg0, hηg, hTg, R', φ', hφ'η, hφ'b⟩ :=
    DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr M 2 η h hηh R₂ hRh hηR₂ κ
      φ₂ hne α hTres

  have h22 : ((2 : ℕ) : ℤ) = 2 := by norm_num
  set g₂ : CuspForm (Gamma1 M) 2 := CuspForm.mcast h22 g with hg₂
  have hg₂coe : ⇑g₂ = ⇑g := rfl
  refine ⟨M, inferInstance, hMprimes, η, g₂, b, ?_, ?_, ?_, R', φ', fun x => (hφ'η x).1,
    fun p hp hpM => (hφ'b p hp hpM (hpκ p hp hpM)).1, fun p hp hpM => ⟨?_, ?_⟩⟩
  ·
    intro h0
    apply hg0
    apply DFunLike.ext
    intro τ
    have := congrArg (fun F : CuspForm (Gamma1 M) 2 => (F : ℍ → ℂ) τ) h0
    simp at this
    exact this
  ·
    intro γ hγ τ
    exact hηg γ hγ τ
  ·
    intro p hp hpM n
    have := hTg p hp hpM n
    rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one] at this
    exact this
  ·
    obtain ⟨hb, hval⟩ := hφ'b p hp hpM (hpκ p hp hpM)
    rw [hval]
    exact hφ₂R (hR p)
  ·
    obtain ⟨hx, hval⟩ := hφ'η (p : ZMod M)
    rw [hval]
    exact hηp p hp hpM

end Engine

noncomputable def chi4 : DirichletCharacter ℂ 4 := (ZMod.χ₄).ringHomComp (Int.castRingHom ℂ)

theorem chi4_apply (x : ZMod 4) : chi4 x = ((ZMod.χ₄ x : ℤ) : ℂ) := rfl

theorem chi4_mem (R : Subalgebra ℤ ℂ) (x : ZMod 4) : chi4 x ∈ R := by
  rw [chi4_apply]; exact intCast_mem R _

theorem chi4_odd : chi4.Odd := by
  rw [DirichletCharacter.Odd, chi4_apply]
  have : ZMod.χ₄ (-1 : ZMod 4) = -1 := by
    have h := ZMod.χ₄_int_three_mod_four (n := -1) (by norm_num)
    rw [Int.cast_neg, Int.cast_one] at h
    exact h
  rw [this]; norm_num

theorem chi4_isPrimitive : chi4.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hne : chi4 ≠ 1 := by
    intro h
    have hodd := chi4_odd
    rw [DirichletCharacter.Odd, h, MulChar.one_apply (isUnit_one.neg)] at hodd
    norm_num at hodd
  have hc1 : chi4.conductor ≠ 1 := fun h =>
    hne (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h)

  have hdvd := DirichletCharacter.conductor_dvd_level chi4
  have hc2 : chi4.conductor ≠ 2 := by
    intro h2
    obtain ⟨hd, χ₀, hχ₀⟩ := DirichletCharacter.factorsThrough_conductor chi4
    apply hne

    have hχ₀1 : ∀ (d : ℕ) (hd2 : d = 2) (ψ : DirichletCharacter ℂ d), ψ = 1 := by
      rintro d rfl ψ
      ext u
      have hu : u = 1 := Subsingleton.elim u 1
      rw [hu, Units.val_one, map_one, map_one]
    have := hχ₀1 _ h2 χ₀
    rw [hχ₀, this, DirichletCharacter.changeLevel_one]
  set c := chi4.conductor with hc
  have hle : c ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases c
  · exact absurd hdvd (by norm_num)
  · exact absurd rfl hc1
  · exact absurd rfl hc2
  · exact absurd hdvd (by norm_num)
  · rfl

theorem chi4_sum : (∑ a ∈ Finset.range 4, (a : ℂ) * chi4 (a : ZMod 4)) = -2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, chi4_apply]
  have h0 : ZMod.χ₄ ((0 : ℕ) : ZMod 4) = 0 := by rw [ZMod.χ₄_nat_eq_if_mod_four]; norm_num
  have h1 : ZMod.χ₄ ((1 : ℕ) : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four (by norm_num)
  have h2 : ZMod.χ₄ ((2 : ℕ) : ZMod 4) = 0 := by rw [ZMod.χ₄_nat_eq_if_mod_four]; norm_num
  have h3 : ZMod.χ₄ ((3 : ℕ) : ZMod 4) = -1 := ZMod.χ₄_nat_three_mod_four (by norm_num)
  rw [h0, h1, h2, h3]
  push_cast
  ring

theorem chi4_natCast_of_odd {p : ℕ} (hp : ¬ 2 ∣ p) :
    chi4 (p : ZMod 4) = 1 ∨ chi4 (p : ZMod 4) = -1 := by
  rw [chi4_apply, ZMod.χ₄_nat_eq_if_mod_four]
  have hodd : p % 2 = 1 := Nat.two_dvd_ne_zero.1 hp
  rw [if_neg (by omega)]
  split_ifs
  · left; norm_num
  · right; norm_num

end DeligneSerreW1W2
p2m_reactivate "P2MW.S_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen.DeligneSerreW1W2"

open DeligneSerreW1W2 ModularFormClass in
theorem solution
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n)
    (R : Subalgebra ℤ ℂ) (hR : ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ R)
    (hε : ∀ x : ZMod N, ε x ∈ R)
    (κ : Type) [Field κ] [Finite κ] (φ : R →+* κ) :
    ∃ (M : ℕ) (_ : NeZero M),
      (∀ p : ℕ, p.Prime → (p ∣ M ↔ p ∣ N ∨ (p : κ) = 0)) ∧
      ∃ (η : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) 2) (b : ℕ → ℂ),
        g ≠ 0 ∧ CuspForm.HasNebentypus η g ∧
        (∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
          ModularFormClass.qCoeff g (p * n) +
              η (p : ZMod M) * (p : ℂ) *
                (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
            b p * ModularFormClass.qCoeff g n) ∧
        ∃ (R' : Subalgebra ℤ ℂ) (φ' : R' →+* κ) (hη : ∀ x : ZMod M, η x ∈ R')
          (hb : ∀ p : ℕ, p.Prime → ¬ p ∣ M → b p ∈ R'),
          ∀ (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M),
            φ' ⟨b p, hb p hp hpM⟩ = φ ⟨ModularFormClass.qCoeff f p, hR p⟩ ∧
            φ' ⟨η (p : ZMod M), hη _⟩ * (p : κ) = φ ⟨ε (p : ZMod N), hε _⟩ := by
  classical

  set ℓ := ringChar κ with hℓ_def
  haveI hchar : CharP κ ℓ := ringChar.charP κ
  have hℓ0 : ℓ ≠ 0 := CharP.ringChar_ne_zero_of_finite κ
  have hℓ : ℓ.Prime := (CharP.char_is_prime_or_zero κ ℓ).resolve_right hℓ0
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓκ : (ℓ : κ) = 0 := CharP.cast_eq_zero κ ℓ
  have hprime_iff : ∀ p : ℕ, p.Prime → ((p : κ) = 0 ↔ p = ℓ) := by
    intro p hp
    constructor
    · intro h
      have hdvd : ℓ ∣ p := (CharP.cast_eq_zero_iff κ ℓ p).1 h
      exact ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 hdvd).symm
    · rintro rfl; exact hℓκ
  by_cases hℓ2 : ℓ = 2
  ·
    have h2κ : (2 : κ) = 0 := by
      have h := hℓκ
      rw [hℓ2] at h
      exact_mod_cast h
    haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
    obtain ⟨E, hEχ, hE0, hEn⟩ :=
      ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd 4 chi4
        chi4_isPrimitive chi4_odd
    have hE0' : qCoeff E 0 = 1 / 4 := by
      rw [hE0, chi4_sum]; norm_num
    have hL : ∀ p : ℕ, p.Prime → (p ∣ 4 ↔ (p : κ) = 0) := by
      intro p hp
      rw [hprime_iff p hp, hℓ2, show (4 : ℕ) = 2 ^ 2 from rfl]
      constructor
      · intro h; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
      · rintro rfl; exact Dvd.intro 2 rfl
    refine engine ε f hf₁ hT R hR hε κ φ hL chi4 E hEχ R (le_refl R) φ (fun z hz => rfl)
      (fun x => chi4_mem R x) ?_ ?_ ?_ 1 (one_mem R) ?_ ?_ ?_
    ·
      intro p hp hp4
      have hp2 : ¬ 2 ∣ p := fun h => hp4 (by
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h
        subst this; norm_num)
      have hpodd : (p : κ) = 1 := by
        obtain ⟨k, hk⟩ := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hp2) |> fun h => (⟨p / 2, by omega⟩ : ∃ k, p = 2 * k + 1)
        rw [hk]; push_cast; rw [h2κ]; ring
      rw [hpodd, mul_one]
      rcases chi4_natCast_of_odd hp2 with h | h
      · have : (⟨chi4 (p : ZMod 4), chi4_mem R _⟩ : R) = 1 := Subtype.ext h
        rw [this, map_one]
      · have : (⟨chi4 (p : ZMod 4), chi4_mem R _⟩ : R) = -1 := Subtype.ext h
        rw [this, map_neg, map_one]

        have : (2 : κ) = 1 + 1 := by norm_num
        rw [this] at h2κ
        exact (neg_eq_of_add_eq_zero_left h2κ)
    ·
      intro m hm
      rw [hEn m hm]
      exact Subalgebra.sum_mem R fun d _ => chi4_mem R _
    · rw [hE0']; norm_num
    · have : (⟨(1 : ℂ), one_mem R⟩ : R) = 1 := rfl
      rw [this, map_one]; exact one_ne_zero
    · rw [hE0', one_mul]
      norm_num
    · have key : ∀ hm : (1 : ℂ) * (qCoeff E 0)⁻¹ ∈ R, φ ⟨(1 : ℂ) * (qCoeff E 0)⁻¹, hm⟩ = 0 := by
        intro hm
        have h4 : (1 : ℂ) * (qCoeff E 0)⁻¹ = ((4 : ℕ) : ℂ) := by rw [hE0']; norm_num
        have : (⟨(1 : ℂ) * (qCoeff E 0)⁻¹, hm⟩ : R) = ((4 : ℕ) : R) := Subtype.ext (by
          rw [SubringClass.coe_natCast]; exact h4)
        rw [this, map_natCast]
        have : ((4 : ℕ) : κ) = 2 * 2 := by norm_num
        rw [this, h2κ, zero_mul]
      exact key _
  ·

    have hℓ1 : ℓ - 1 ≠ 0 := by have := hℓ.two_le; omega
    haveI : NeZero ℓ := ⟨hℓ0⟩

    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (ℓ - 1 : ℕ)) with hζ_def
    have hζ : IsPrimitiveRoot ζ (ℓ - 1) := Complex.isPrimitiveRoot_exp (ℓ - 1) hℓ1
    have hζpow : ζ ^ (ℓ - 1) = 1 := hζ.pow_eq_one
    have hRR₁ : R ≤ adjoinRoot' R ζ := le_adjoinRoot' R ζ
    have hζR : ζ ∈ adjoinRoot' R ζ := self_mem_adjoinRoot' R ζ
    obtain ⟨φ₁, hφ₁⟩ := exists_ringHom_adjoinRoot'_extends R φ ζ hζpow

    haveI : NeZero ((ℓ - 1 : ℕ) : κ) := ⟨by
      rw [Nat.cast_sub hℓ.one_lt.le, Nat.cast_one, hℓκ, zero_sub]
      exact neg_ne_zero.2 one_ne_zero⟩
    have hμ : IsPrimitiveRoot (φ₁ ⟨ζ, hζR⟩) (ℓ - 1) :=
      isPrimitiveRoot_map_of_isPrimitiveRoot φ₁ hζ hζR

    set χ : DirichletCharacter ℂ ℓ := teich φ₁ hζ hζR hμ with hχ_def
    obtain ⟨E, hEχ, hE0, hEn⟩ :=
      ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd ℓ χ
        (teich_isPrimitive φ₁ hζ hζR hμ hℓ2) (teich_odd φ₁ hζ hζR hμ hℓ2)
    set S : ℂ := ∑ a ∈ Finset.range ℓ, (a : ℂ) * χ (a : ZMod ℓ) with hS_def
    have hSmem : S ∈ adjoinRoot' R ζ := teichSum_mem φ₁ hζ hζR hμ
    have hSred : φ₁ ⟨S, hSmem⟩ = -1 := map_sum_eq_neg_one φ₁ hζ hζR hμ
    have hS0 : S ≠ 0 := by
      intro h
      have : (⟨S, hSmem⟩ : adjoinRoot' R ζ) = 0 := Subtype.ext h
      rw [this, map_zero] at hSred
      exact one_ne_zero (neg_eq_zero.1 hSred.symm)
    have hE0' : qCoeff E 0 = -S / (2 * ℓ) := hE0
    have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ0
    have hL : ∀ p : ℕ, p.Prime → (p ∣ ℓ ↔ (p : κ) = 0) := by
      intro p hp
      rw [hprime_iff p hp, Nat.prime_dvd_prime_iff_eq hp hℓ]
    refine engine ε f hf₁ hT R hR hε κ φ hL χ E hEχ (adjoinRoot' R ζ) hRR₁ φ₁ hφ₁
      (fun x => teich_mem φ₁ hζ hζR hμ x) ?_ ?_ ?_ S hSmem ?_ ?_ ?_
    ·
      intro p hp hpℓ
      have hℓp : ¬ ℓ ∣ p := fun h => hpℓ (by
        rw [(Nat.prime_dvd_prime_iff_eq hℓ hp).1 h])
      exact map_teich_natCast_mul φ₁ hζ hζR hμ hℓp
    ·
      intro m hm
      rw [hEn m hm]
      exact Subalgebra.sum_mem _ fun d _ => teich_mem φ₁ hζ hζR hμ _
    · rw [hE0']
      exact div_ne_zero (neg_ne_zero.2 hS0) (mul_ne_zero two_ne_zero hℓC)
    · rw [hSred]; exact neg_ne_zero.2 one_ne_zero
    ·
      rw [hE0']
      have : S * (-S / (2 * ℓ))⁻¹ = -(2 * ℓ) := by
        field_simp
      rw [this]
      exact neg_mem (mul_mem (by exact_mod_cast natCast_mem (adjoinRoot' R ζ) 2)
        (natCast_mem (adjoinRoot' R ζ) ℓ))
    ·
      have hval : S * (qCoeff E 0)⁻¹ = ((2 * ℓ : ℕ) : ℂ) * (-1) := by
        rw [hE0']; push_cast; field_simp
      have key : ∀ hm : S * (qCoeff E 0)⁻¹ ∈ adjoinRoot' R ζ,
          φ₁ ⟨S * (qCoeff E 0)⁻¹, hm⟩ = 0 := by
        intro hm
        have : (⟨S * (qCoeff E 0)⁻¹, hm⟩ : adjoinRoot' R ζ) =
            ((2 * ℓ : ℕ) : adjoinRoot' R ζ) * (-1) := Subtype.ext (by
          rw [Subalgebra.coe_mul, SubringClass.coe_natCast, Subalgebra.coe_neg, Subalgebra.coe_one]
          exact hval)
        rw [this, map_mul, map_natCast, Nat.cast_mul, hℓκ, mul_zero, zero_mul]
      exact key _

end S_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen
end P2MW
export P2MW.S_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen (solution)
