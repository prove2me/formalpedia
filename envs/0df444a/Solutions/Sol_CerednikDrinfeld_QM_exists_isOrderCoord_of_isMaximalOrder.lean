-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_isOrderCoord_of_isMaximalOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/9fc6cd5d-ca26-53fe-8bde-22a7386b4d66

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Theorems.Thm_WittVector_exists_ringHom_padicInt_and_root_of_forall_sq_sub_mul_add_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_trd_eq_nrd_eq_forall_sq_sub_mul_add_ne_zero_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_exists_sq_eq_natCast_and_setOf_norm_nrd_le_one_eq_of_forall_isUnit_padic
import Theorems.Thm_PadicInt_exists_sq_add_mul_add_mul_sq_eq_of_isUnit_of_forall_ne_zero
import Theorems.Thm_Submodule_exists_mem_add_one_tmul_pow_mul_of_mem_localBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_ringEquiv_coe_localBox_eq_setOf_norm_nrd_le_one_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_isOrderCoord_of_isMaximalOrder
p2m_attr_erase "simp" "QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option linter.style.longFile 0
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

noncomputable section

namespace OrderCoord

section Algebra

variable {K : Type*} [Field K] {A B : K}

theorem nrd_mul' (x y : ℍ[K, A, B]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]
  ring

theorem nrd_add' (x y : ℍ[K, A, B]) : nrd (x + y) = nrd x + nrd y + trd (x * star y) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk, nrd_mk, trd_mk]
  ring

theorem trd_add' (x y : ℍ[K, A, B]) : trd (x + y) = trd x + trd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_add_mk, trd_mk]
  ring

theorem trd_mul_comm' (x y : ℍ[K, A, B]) : trd (x * y) = trd (y * x) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, trd_mk]
  ring

theorem trd_sub' (x y : ℍ[K, A, B]) : trd (x - y) = trd x - trd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_sub_mk, trd_mk]
  ring

theorem trd_neg' (x : ℍ[K, A, B]) : trd (-x) = -trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.neg_mk, trd_mk]
  ring

theorem coe_eq_mk (c : K) : ((c : K) : ℍ[K, A, B]) = ⟨c, 0, 0, 0⟩ := rfl

theorem trd_coe' (c : K) : trd ((c : K) : ℍ[K, A, B]) = 2 * c := by
  rw [coe_eq_mk, trd_mk]

theorem nrd_coe' (c : K) : nrd ((c : K) : ℍ[K, A, B]) = c ^ 2 := by
  rw [coe_eq_mk, nrd_mk]; ring

theorem trd_coe_mul' (c : K) (x : ℍ[K, A, B]) : trd ((c : ℍ[K, A, B]) * x) = c * trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  rw [coe_eq_mk, QuaternionAlgebra.mk_mul_mk, trd_mk, trd_mk]
  ring

theorem nrd_coe_mul' (c : K) (x : ℍ[K, A, B]) : nrd ((c : ℍ[K, A, B]) * x) = c ^ 2 * nrd x := by
  rw [nrd_mul', nrd_coe']

theorem star_coe' (c : K) : star ((c : K) : ℍ[K, A, B]) = c := by
  rw [coe_eq_mk, QuaternionAlgebra.star_mk]; ext <;> simp

theorem sq_eq_trd_mul_sub_nrd (x : ℍ[K, A, B]) :
    x * x = ((trd x : K) : ℍ[K, A, B]) * x - ((nrd x : K) : ℍ[K, A, B]) := by
  have h1 : x + star x = ((trd x : K) : ℍ[K, A, B]) := add_star_eq_coe_trd x
  have h2 : x * star x = ((nrd x : K) : ℍ[K, A, B]) := mul_star_eq_coe_nrd x
  have h3 : star x = ((trd x : K) : ℍ[K, A, B]) - x := by rw [← h1, add_sub_cancel_left]
  rw [h3, mul_sub, ← QuaternionAlgebra.coe_commutes] at h2

  rw [← h2]
  abel

theorem intCast_eq_coe (z : ℤ) : ((z : ℤ) : ℍ[K, A, B]) = ((z : K) : ℍ[K, A, B]) := by
  ext <;> simp

theorem natCast_eq_coe (m : ℕ) : ((m : ℕ) : ℍ[K, A, B]) = ((m : K) : ℍ[K, A, B]) := by
  ext <;> simp

section Division

variable (hD : ∀ x : ℍ[K, A, B], x ≠ 0 → IsUnit x)
include hD

theorem nrd_ne_zero_of_ne_zero {x : ℍ[K, A, B]} (hx : x ≠ 0) : nrd x ≠ 0 := by
  intro h0
  have h2 : x * star x = 0 := by rw [mul_star_eq_coe_nrd, h0]; rfl
  have hs : star x = 0 := (hD x hx).mul_right_eq_zero.1 h2
  apply hx
  have := congrArg star hs
  rwa [star_star, star_zero] at this

theorem eq_zero_of_nrd_eq_zero {x : ℍ[K, A, B]} (h : nrd x = 0) : x = 0 := by
  by_contra hx
  exact nrd_ne_zero_of_ne_zero hD hx h

theorem eq_zero_or_eq_zero_of_mul_eq_zero {x y : ℍ[K, A, B]} (h : x * y = 0) : x = 0 ∨ y = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr ((hD x hx).mul_right_eq_zero.1 h)

theorem trd_eq_and_nrd_eq_of_sq_eq {x : ℍ[K, A, B]} (hx : ∀ c : K, x ≠ (c : ℍ[K, A, B]))
    {s r : K} (h : x * x = ((s : K) : ℍ[K, A, B]) * x - ((r : K) : ℍ[K, A, B])) :
    trd x = s ∧ nrd x = r := by
  have hch := sq_eq_trd_mul_sub_nrd x

  have e : ((trd x : K) : ℍ[K, A, B]) * x - ((nrd x : K) : ℍ[K, A, B]) =
      ((s : K) : ℍ[K, A, B]) * x - ((r : K) : ℍ[K, A, B]) := hch.symm.trans h
  have key : (((trd x - s : K)) : ℍ[K, A, B]) * x = (((nrd x - r : K)) : ℍ[K, A, B]) := by
    rw [QuaternionAlgebra.coe_sub, QuaternionAlgebra.coe_sub, sub_mul]
    calc ((trd x : K) : ℍ[K, A, B]) * x - ((s : K) : ℍ[K, A, B]) * x
        = (((trd x : K) : ℍ[K, A, B]) * x - ((nrd x : K) : ℍ[K, A, B]))
            - (((s : K) : ℍ[K, A, B]) * x - ((r : K) : ℍ[K, A, B]))
            + (((nrd x : K) : ℍ[K, A, B]) - ((r : K) : ℍ[K, A, B])) := by abel
      _ = ((nrd x : K) : ℍ[K, A, B]) - ((r : K) : ℍ[K, A, B]) := by rw [e, sub_self, zero_add]
  by_cases hts : trd x - s = 0
  · have h1 : trd x = s := sub_eq_zero.1 hts
    refine ⟨h1, ?_⟩
    rw [hts, QuaternionAlgebra.coe_zero, zero_mul, ← QuaternionAlgebra.coe_zero] at key
    have := QuaternionAlgebra.coe_injective key
    exact (sub_eq_zero.1 this.symm)
  · exfalso
    apply hx ((trd x - s)⁻¹ * (nrd x - r))
    have h1 : x = (((trd x - s)⁻¹ : K) : ℍ[K, A, B]) * ((((trd x - s : K)) : ℍ[K, A, B]) * x) := by
      rw [← mul_assoc, ← QuaternionAlgebra.coe_mul, inv_mul_cancel₀ hts, QuaternionAlgebra.coe_one, one_mul]
    calc x = (((trd x - s)⁻¹ : K) : ℍ[K, A, B]) * ((((trd x - s : K)) : ℍ[K, A, B]) * x) := h1
      _ = (((trd x - s)⁻¹ : K) : ℍ[K, A, B]) * (((nrd x - r : K)) : ℍ[K, A, B]) := by rw [key]
      _ = ((((trd x - s)⁻¹ * (nrd x - r) : K)) : ℍ[K, A, B]) := by rw [QuaternionAlgebra.coe_mul]

theorem trd_eq_zero_of_sq_eq_coe {x : ℍ[K, A, B]} (hx : ∀ c : K, x ≠ (c : ℍ[K, A, B]))
    {d : K} (h : x * x = ((d : K) : ℍ[K, A, B])) : trd x = 0 ∧ nrd x = -d := by
  have := trd_eq_and_nrd_eq_of_sq_eq hD hx (s := 0) (r := -d)
    (by rw [h, QuaternionAlgebra.coe_zero, zero_mul, QuaternionAlgebra.coe_neg, zero_sub, neg_neg])
  exact this

end Division

end Algebra

section Quadratic

variable {K : Type*} [Field K] {A B : K}
variable (t n : K) (θ ϖ : ℍ[K, A, B])

def ell (c d : K) : ℍ[K, A, B] := ((c : K) : ℍ[K, A, B]) + ((d : K) : ℍ[K, A, B]) * θ

def combo (c₀ c₁ c₂ c₃ : K) : ℍ[K, A, B] :=
  ((c₀ : K) : ℍ[K, A, B]) + ((c₁ : K) : ℍ[K, A, B]) * θ + ((c₂ : K) : ℍ[K, A, B]) * ϖ
    + ((c₃ : K) : ℍ[K, A, B]) * (θ * ϖ)

theorem combo_eq (c₀ c₁ c₂ c₃ : K) : combo θ ϖ c₀ c₁ c₂ c₃ = ell θ c₀ c₁ + ell θ c₂ c₃ * ϖ := by
  simp only [combo, ell, add_mul, mul_assoc]; abel

theorem combo_add (c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : K) :
    combo θ ϖ c₀ c₁ c₂ c₃ + combo θ ϖ d₀ d₁ d₂ d₃ = combo θ ϖ (c₀ + d₀) (c₁ + d₁) (c₂ + d₂) (c₃ + d₃) := by
  simp only [combo, QuaternionAlgebra.coe_add, add_mul]; abel

theorem combo_sub (c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : K) :
    combo θ ϖ c₀ c₁ c₂ c₃ - combo θ ϖ d₀ d₁ d₂ d₃ = combo θ ϖ (c₀ - d₀) (c₁ - d₁) (c₂ - d₂) (c₃ - d₃) := by
  simp only [combo, QuaternionAlgebra.coe_sub, sub_mul]; abel

theorem coe_mul_combo (s c₀ c₁ c₂ c₃ : K) :
    ((s : K) : ℍ[K, A, B]) * combo θ ϖ c₀ c₁ c₂ c₃ = combo θ ϖ (s * c₀) (s * c₁) (s * c₂) (s * c₃) := by
  simp only [combo, QuaternionAlgebra.coe_mul, mul_add, mul_assoc]

theorem combo_congr {c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : K} (h₀ : c₀ = d₀) (h₁ : c₁ = d₁) (h₂ : c₂ = d₂) (h₃ : c₃ = d₃) :
    combo θ ϖ c₀ c₁ c₂ c₃ = combo θ ϖ d₀ d₁ d₂ d₃ := by
  subst h₀ h₁ h₂ h₃; rfl

theorem combo_one : combo θ ϖ 1 0 0 0 = 1 := by simp [combo]

theorem ell_add (c d c' d' : K) : ell θ c d + ell θ c' d' = ell θ (c + c') (d + d') := by
  simp only [ell, QuaternionAlgebra.coe_add, add_mul]; abel

theorem coe_mul_ell (s c d : K) : ((s : K) : ℍ[K, A, B]) * ell θ c d = ell θ (s * c) (s * d) := by
  simp only [ell, QuaternionAlgebra.coe_mul, mul_add, mul_assoc]

theorem ell_mul_coe (s c d : K) : ell θ c d * ((s : K) : ℍ[K, A, B]) = ell θ (s * c) (s * d) := by
  rw [← QuaternionAlgebra.coe_commutes, coe_mul_ell]

theorem ell_mul_theta' (c d : K) : ell θ c d * θ = θ * ell θ c d := by
  obtain ⟨θ₀, θ₁, θ₂, θ₃⟩ := θ
  ext <;> simp [ell, coe_eq_mk] <;> ring

theorem ell_mul_ell' (hsq : θ * θ = ((t : K) : ℍ[K, A, B]) * θ - ((n : K) : ℍ[K, A, B])) (c₀ c₁ c₂ c₃ : K) :
    ell θ c₀ c₁ * ell θ c₂ c₃ = ell θ (c₀ * c₂ - n * c₁ * c₃) (c₀ * c₃ + c₁ * c₂ + t * c₁ * c₃) := by
  obtain ⟨θ₀, θ₁, θ₂, θ₃⟩ := θ
  have hre := congrArg QuaternionAlgebra.re hsq
  have hI := congrArg QuaternionAlgebra.imI hsq
  have hJ := congrArg QuaternionAlgebra.imJ hsq
  have hK' := congrArg QuaternionAlgebra.imK hsq
  simp [coe_eq_mk] at hre hI hJ hK'
  ext <;> simp [ell, coe_eq_mk]
  · linear_combination (c₁ * c₃) * hre
  · linear_combination (c₁ * c₃) * hI
  · linear_combination (c₁ * c₃) * hJ
  · linear_combination (c₁ * c₃) * hK'

theorem varpi_mul_ell' (hϖθ : ϖ * θ = (((t : K) : ℍ[K, A, B]) - θ) * ϖ) (c d : K) :
    ϖ * ell θ c d = ell θ (c + d * t) (-d) * ϖ := by
  simp only [ell, mul_add, add_mul, QuaternionAlgebra.coe_add, QuaternionAlgebra.coe_mul, QuaternionAlgebra.coe_neg]
  rw [← QuaternionAlgebra.coe_commutes c ϖ, ← mul_assoc, ← QuaternionAlgebra.coe_commutes d ϖ, mul_assoc, hϖθ]
  simp only [sub_mul, mul_sub, mul_assoc, neg_mul]
  abel

theorem trd_combo (htrθ : trd θ = t) (htrϖ : trd ϖ = 0) (htrθϖ : trd (θ * ϖ) = 0) (c₀ c₁ c₂ c₃ : K) :
    trd (combo θ ϖ c₀ c₁ c₂ c₃) = 2 * c₀ + t * c₁ := by
  simp only [combo, trd_add', trd_coe_mul', trd_coe', htrθ, htrϖ, htrθϖ]
  ring

end Quadratic

section ComboMul

variable {K : Type*} [Field K] {A B : K}
variable (t n P : K) (θ ϖ : ℍ[K, A, B])
  (hsq : θ * θ = ((t : K) : ℍ[K, A, B]) * θ - ((n : K) : ℍ[K, A, B]))
  (hϖθ : ϖ * θ = (((t : K) : ℍ[K, A, B]) - θ) * ϖ)
  (hϖsq : ϖ * ϖ = ((P : K) : ℍ[K, A, B]))
include hsq hϖθ hϖsq

theorem combo_mul (c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : K) :
    combo θ ϖ c₀ c₁ c₂ c₃ * combo θ ϖ d₀ d₁ d₂ d₃ =
      combo θ ϖ
        ((c₀ * d₀ - n * c₁ * d₁) + P * (c₂ * (d₂ + d₃ * t) - n * c₃ * (-d₃)))
        ((c₀ * d₁ + c₁ * d₀ + t * c₁ * d₁) + P * (c₂ * (-d₃) + c₃ * (d₂ + d₃ * t) + t * c₃ * (-d₃)))
        ((c₀ * d₂ - n * c₁ * d₃) + (c₂ * (d₀ + d₁ * t) - n * c₃ * (-d₁)))
        ((c₀ * d₃ + c₁ * d₂ + t * c₁ * d₃) + (c₂ * (-d₁) + c₃ * (d₀ + d₁ * t) + t * c₃ * (-d₁))) := by
  set L1 := ell θ c₀ c₁ with hL1
  set L2 := ell θ c₂ c₃ with hL2
  set M1 := ell θ d₀ d₁ with hM1
  set M2 := ell θ d₂ d₃ with hM2
  have T2 : L1 * (M2 * ϖ) = (L1 * M2) * ϖ := (mul_assoc _ _ _).symm
  have T3 : L2 * ϖ * M1 = (L2 * ell θ (d₀ + d₁ * t) (-d₁)) * ϖ := by
    rw [mul_assoc, hM1, varpi_mul_ell' t θ ϖ hϖθ, ← mul_assoc]
  have T4 : L2 * ϖ * (M2 * ϖ) = ((P : K) : ℍ[K, A, B]) * (L2 * ell θ (d₂ + d₃ * t) (-d₃)) := by
    calc L2 * ϖ * (M2 * ϖ) = L2 * ((ϖ * M2) * ϖ) := by simp only [mul_assoc]
      _ = L2 * ((ell θ (d₂ + d₃ * t) (-d₃) * ϖ) * ϖ) := by rw [hM2, varpi_mul_ell' t θ ϖ hϖθ]
      _ = (L2 * ell θ (d₂ + d₃ * t) (-d₃)) * (ϖ * ϖ) := by simp only [mul_assoc]
      _ = ((P : K) : ℍ[K, A, B]) * (L2 * ell θ (d₂ + d₃ * t) (-d₃)) := by
          rw [hϖsq, ← QuaternionAlgebra.coe_commutes]
  rw [combo_eq, combo_eq, combo_eq, ← hL1, ← hL2, ← hM1, ← hM2, add_mul, mul_add, mul_add, T2, T3, T4,
    hL1, hL2, hM1, hM2, ell_mul_ell' t n θ hsq, ell_mul_ell' t n θ hsq, ell_mul_ell' t n θ hsq, ell_mul_ell' t n θ hsq,
    coe_mul_ell]
  rw [show ∀ (X Y Z W : ℍ[K, A, B]), X + Y * ϖ + (Z * ϖ + W) = (X + W) + (Y + Z) * ϖ by
    intro X Y Z W; rw [add_mul]; abel]
  rw [ell_add, ell_add]

end ComboMul

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ) :
    (m : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ m := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) m, Ideal.apply_mem_of_equiv_iff]

section Main

variable (v : HeightOneSpectrum (𝓞 ℚ)) [hF : Fact (Nat.Prime (Rat.HeightOneSpectrum.natGenerator v))]
variable {a b : ℚ} {q' : ℕ} [Fact q'.Prime]

theorem main (hB : IsIndefiniteRamifiedExactlyAt a b (Rat.HeightOneSpectrum.natGenerator v) q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :
    ∃ coord : ↥Λ → CerednikDrinfeld.Zp2 (Rat.HeightOneSpectrum.natGenerator v) × CerednikDrinfeld.Zp2 (Rat.HeightOneSpectrum.natGenerator v),
      CerednikDrinfeld.QM.IsOrderCoord Λ (Rat.HeightOneSpectrum.natGenerator v) coord := by
  classical
  have hp : (Rat.HeightOneSpectrum.natGenerator v).Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  have hO : IsOrder Λ := hΛ.isOrder
  have hpv : ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := (natCast_mem_asIdeal_iff v _).2 dvd_rfl

  have hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x := (hB.2 v).2 (Or.inl hpv)

  haveI hF' : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ)) := ⟨hp⟩
  obtain ⟨Θ, hΘ1, hΘbox⟩ : ∃ Θ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])],
      (∀ c : v.adicCompletion ℚ, Θ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) =
        (@id ℚ_[Rat.HeightOneSpectrum.natGenerator v] (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) v c)) • (1 : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])])) ∧
      ((Submodule.localBox Λ v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) :
          Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) = {x | ‖QuaternionAlgebra.nrd (Θ x)‖ ≤ 1} :=
    QuaternionAlgebra.IsMaximalOrder.exists_ringEquiv_coe_localBox_eq_setOf_norm_nrd_le_one_of_forall_isUnit hΛ v hdiv
  have hD : ∀ x : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])], x ≠ 0 → IsUnit x := by
    intro x hx
    have h1 : Θ.symm x ≠ 0 := by
      intro h0; apply hx; simpa using congrArg Θ h0
    have := (hdiv _ h1).map Θ
    simpa using this

  obtain ⟨θ₀, hθ₀Λ, t, n, hθ₀t, hθ₀n, hirr⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_mem_trd_eq_nrd_eq_forall_sq_sub_mul_add_ne_zero_of_isIndefiniteRamifiedExactlyAt
      hB Λ hΛ (Rat.HeightOneSpectrum.natGenerator v) (Or.inl rfl)

  set Ψ : ℍ[ℚ, a, b] →+* ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])] := Θ.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom with hΨdef
  have hΨ : ∀ m : ℍ[ℚ, a, b], Ψ m = Θ (m ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) := fun _ => rfl
  have hΨcoe : ∀ r : ℚ, Ψ ((r : ℚ) : ℍ[ℚ, a, b]) = (((r : ℚ_[Rat.HeightOneSpectrum.natGenerator v])) : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])]) := by
    intro r
    rw [hΨ]
    have e1 : ((r : ℚ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)
        = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (algebraMap ℚ (v.adicCompletion ℚ) r) := by
      rw [show ((r : ℚ) : ℍ[ℚ, a, b]) = r • (1 : ℍ[ℚ, a, b]) by rw [← QuaternionAlgebra.coe_mul_eq_smul, mul_one],
        TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    rw [e1, hΘ1, AlgHomClass.commutes, ← QuaternionAlgebra.coe_mul_eq_smul, mul_one]
    simp
    try rfl

  set θ : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])] := Ψ θ₀ with hθdef
  have hsqB : θ₀ * θ₀ = (((t : ℚ)) : ℍ[ℚ, a, b]) * θ₀ - (((n : ℚ)) : ℍ[ℚ, a, b]) := by
    rw [sq_eq_trd_mul_sub_nrd θ₀, hθ₀t, hθ₀n]
  have htQ : (((t : ℚ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v])) = ((t : ℤ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) := by push_cast; rfl
  have hnQ : (((n : ℚ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v])) = ((n : ℤ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) := by push_cast; rfl
  have hθsq : θ * θ = ((((t : ℤ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v])) : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])]) * θ - ((((n : ℤ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v])) : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])]) := by
    have := congrArg Ψ hsqB
    rw [map_mul, map_sub, map_mul, hΨcoe, hΨcoe, htQ, hnQ] at this
    rw [hθdef]; exact this
  have hθ : θ * θ - (t : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])]) * θ + (n : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])]) = 0 := by
    rw [hθsq, intCast_eq_coe, intCast_eq_coe]; abel

  have hN := PadicInt.exists_sq_add_mul_add_mul_sq_eq_of_isUnit_of_forall_ne_zero (Rat.HeightOneSpectrum.natGenerator v) t n hirr
  obtain ⟨ϖ, hϖsq, hϖθ', htrθ, hnrθ, htrϖ, htrθϖ, hindep, horder⟩ :=
    QuaternionAlgebra.exists_sq_eq_natCast_and_setOf_norm_nrd_le_one_eq_of_forall_isUnit_padic (Rat.HeightOneSpectrum.natGenerator v) hD t n hirr hN θ hθ
  have hϖθ : ϖ * θ = (((((t : ℤ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v])) : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])]) - θ) * ϖ := by rw [← intCast_eq_coe]; exact hϖθ'
  obtain ⟨ι, ω, hιfrob, hωsq, hωfrob, hιinj, hdense⟩ :=
    WittVector.exists_ringHom_padicInt_and_root_of_forall_sq_sub_mul_add_ne_zero (Rat.HeightOneSpectrum.natGenerator v) t n hirr

  have hΨbox : ∀ m : ↥Λ, ‖nrd (Ψ (m : ℍ[ℚ, a, b]))‖ ≤ 1 := by
    intro m
    have h1 : (m : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈
        ((Submodule.localBox Λ v : AddSubgroup _) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) :=
      AddSubgroup.subset_closure ⟨m, m.2, 1, (v.adicCompletionIntegers ℚ).one_mem, rfl⟩
    rw [hΘbox] at h1
    exact h1

  have huniqQ : ∀ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : ℚ_[Rat.HeightOneSpectrum.natGenerator v],
      combo θ ϖ c₀ c₁ c₂ c₃ = combo θ ϖ d₀ d₁ d₂ d₃ → c₀ = d₀ ∧ c₁ = d₁ ∧ c₂ = d₂ ∧ c₃ = d₃ := by
    intro c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ h
    have h' : combo θ ϖ (c₀ - d₀) (c₁ - d₁) (c₂ - d₂) (c₃ - d₃) = 0 := by rw [← combo_sub, h, sub_self]
    obtain ⟨h0, h1, h2, h3⟩ := hindep _ _ _ _ h'
    exact ⟨sub_eq_zero.1 h0, sub_eq_zero.1 h1, sub_eq_zero.1 h2, sub_eq_zero.1 h3⟩
  have hex : ∀ m : ↥Λ, ∃ c : (ℤ_[Rat.HeightOneSpectrum.natGenerator v] × ℤ_[Rat.HeightOneSpectrum.natGenerator v]) × (ℤ_[Rat.HeightOneSpectrum.natGenerator v] × ℤ_[Rat.HeightOneSpectrum.natGenerator v]),
      Ψ (m : ℍ[ℚ, a, b]) = combo θ ϖ (c.1.1 : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (c.1.2 : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (c.2.1 : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (c.2.2 : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) := by
    intro m
    obtain ⟨c₀, c₁, c₂, c₃, hc⟩ := (horder _).1 (hΨbox m)
    exact ⟨((c₀, c₁), (c₂, c₃)), hc⟩
  choose κ hκ using hex
  have hκuniq : ∀ (m : ↥Λ) (c₀ c₁ c₂ c₃ : ℤ_[Rat.HeightOneSpectrum.natGenerator v]),
      Ψ (m : ℍ[ℚ, a, b]) = combo θ ϖ (c₀ : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (c₁ : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (c₂ : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (c₃ : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) →
      κ m = ((c₀, c₁), (c₂, c₃)) := by
    intro m c₀ c₁ c₂ c₃ h
    rw [hκ m] at h
    obtain ⟨h0, h1, h2, h3⟩ := huniqQ _ _ _ _ _ _ _ _ h
    ext
    · exact Subtype.ext h0
    · exact Subtype.ext h1
    · exact Subtype.ext h2
    · exact Subtype.ext h3

  refine ⟨fun m => (ι (κ m).1.1 + ι (κ m).1.2 * ω, ι (κ m).2.1 + ι (κ m).2.2 * ω), ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro m m'
    have hsum : Ψ ((m + m' : ↥Λ) : ℍ[ℚ, a, b]) = combo θ ϖ
        (((κ m).1.1 + (κ m').1.1 : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (((κ m).1.2 + (κ m').1.2 : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v])
        (((κ m).2.1 + (κ m').2.1 : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (((κ m).2.2 + (κ m').2.2 : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) := by
      rw [Submodule.coe_add, map_add, hκ m, hκ m', combo_add]; push_cast; ring_nf
    have hk := hκuniq _ _ _ _ _ hsum
    apply Prod.ext
    · dsimp only [Prod.fst_add]
      rw [hk]; dsimp only; rw [map_add, map_add]; ring
    · dsimp only [Prod.snd_add]
      rw [hk]; dsimp only; rw [map_add, map_add]; ring
  ·
    intro h1
    have hone : Ψ ((⟨1, h1⟩ : ↥Λ) : ℍ[ℚ, a, b]) = combo θ ϖ ((1 : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) ((0 : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v])
        ((0 : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) ((0 : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) := by
      rw [Submodule.coe_mk, map_one]; push_cast; rw [combo_one]
    have hk := hκuniq _ _ _ _ _ hone
    simp only [hk, map_one, map_zero, zero_mul, add_zero]
  ·
    intro m m' hmm
    have hϖsq' : ϖ * ϖ = ((((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v])) : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])]) := by rw [hϖsq, natCast_eq_coe]
    obtain ⟨pp, hpp⟩ : ∃ pp : ℤ_[Rat.HeightOneSpectrum.natGenerator v], pp = ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) := ⟨_, rfl⟩
    obtain ⟨tt, htt⟩ : ∃ tt : ℤ_[Rat.HeightOneSpectrum.natGenerator v], tt = ((t : ℤ) : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) := ⟨_, rfl⟩
    obtain ⟨nn, hnn⟩ : ∃ nn : ℤ_[Rat.HeightOneSpectrum.natGenerator v], nn = ((n : ℤ) : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : (ℤ_[Rat.HeightOneSpectrum.natGenerator v] × ℤ_[Rat.HeightOneSpectrum.natGenerator v]) × (ℤ_[Rat.HeightOneSpectrum.natGenerator v] × ℤ_[Rat.HeightOneSpectrum.natGenerator v]), c = κ m := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d : (ℤ_[Rat.HeightOneSpectrum.natGenerator v] × ℤ_[Rat.HeightOneSpectrum.natGenerator v]) × (ℤ_[Rat.HeightOneSpectrum.natGenerator v] × ℤ_[Rat.HeightOneSpectrum.natGenerator v]), d = κ m' := ⟨_, rfl⟩
    obtain ⟨P₀, hP₀⟩ : ∃ P₀ : ℤ_[Rat.HeightOneSpectrum.natGenerator v], P₀ = (c.1.1 * d.1.1 - nn * c.1.2 * d.1.2)
        + pp * (c.2.1 * (d.2.1 + d.2.2 * tt) - nn * c.2.2 * (-d.2.2)) := ⟨_, rfl⟩
    obtain ⟨P₁, hP₁⟩ : ∃ P₁ : ℤ_[Rat.HeightOneSpectrum.natGenerator v], P₁ = (c.1.1 * d.1.2 + c.1.2 * d.1.1 + tt * c.1.2 * d.1.2)
        + pp * (c.2.1 * (-d.2.2) + c.2.2 * (d.2.1 + d.2.2 * tt) + tt * c.2.2 * (-d.2.2)) := ⟨_, rfl⟩
    obtain ⟨P₂, hP₂⟩ : ∃ P₂ : ℤ_[Rat.HeightOneSpectrum.natGenerator v], P₂ = (c.1.1 * d.2.1 - nn * c.1.2 * d.2.2)
        + (c.2.1 * (d.1.1 + d.1.2 * tt) - nn * c.2.2 * (-d.1.2)) := ⟨_, rfl⟩
    obtain ⟨P₃, hP₃⟩ : ∃ P₃ : ℤ_[Rat.HeightOneSpectrum.natGenerator v], P₃ = (c.1.1 * d.2.2 + c.1.2 * d.2.1 + tt * c.1.2 * d.2.2)
        + (c.2.1 * (-d.1.2) + c.2.2 * (d.1.1 + d.1.2 * tt) + tt * c.2.2 * (-d.1.2)) := ⟨_, rfl⟩
    have hP : Ψ (((⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), hmm⟩ : ↥Λ) : ℍ[ℚ, a, b])) =
        combo θ ϖ (P₀ : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (P₁ : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (P₂ : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (P₃ : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) := by
      rw [Submodule.coe_mk, map_mul, hκ m, hκ m', ← hc, ← hd,
        combo_mul ((t : ℤ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) ((n : ℤ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) θ ϖ hθsq hϖθ hϖsq']
      apply combo_congr
      · simp only [hP₀, hpp, htt, hnn]; push_cast; ring
      · simp only [hP₁, hpp, htt, hnn]; push_cast; ring
      · simp only [hP₂, hpp, htt, hnn]; push_cast; ring
      · simp only [hP₃, hpp, htt, hnn]; push_cast; ring
    have hk := hκuniq _ _ _ _ _ hP
    apply Prod.ext
    · dsimp only
      rw [hk, ← hc, ← hd]; dsimp only
      simp only [hP₀, hP₁, hpp, htt, hnn]
      simp only [map_add, map_mul, map_sub, map_neg, map_natCast, map_intCast, hιfrob, hωfrob]
      linear_combination (((Rat.HeightOneSpectrum.natGenerator v : ℕ) : CerednikDrinfeld.Zp2 (Rat.HeightOneSpectrum.natGenerator v)) * ι c.2.2 * ι d.2.2 - ι c.1.2 * ι d.1.2) * hωsq
    · dsimp only
      rw [hk, ← hc, ← hd]; dsimp only
      simp only [hP₂, hP₃, htt, hnn]
      simp only [map_add, map_mul, map_sub, map_neg, map_natCast, map_intCast, hιfrob, hωfrob]
      linear_combination (ι c.2.2 * ι d.1.2 - ι c.1.2 * ι d.2.2) * hωsq
  ·
    intro m m' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : ι ((κ m).1.1 - (κ m').1.1) + ι ((κ m).1.2 - (κ m').1.2) * ω = 0 := by
      rw [map_sub, map_sub, sub_mul]; linear_combination h1
    have e2 : ι ((κ m).2.1 - (κ m').2.1) + ι ((κ m).2.2 - (κ m').2.2) * ω = 0 := by
      rw [map_sub, map_sub, sub_mul]; linear_combination h2
    obtain ⟨a1, a2⟩ := hιinj _ _ e1
    obtain ⟨a3, a4⟩ := hιinj _ _ e2
    have hκeq : κ m = κ m' := by
      ext
      · exact sub_eq_zero.1 a1
      · exact sub_eq_zero.1 a2
      · exact sub_eq_zero.1 a3
      · exact sub_eq_zero.1 a4
    have hΨeq : Ψ (m : ℍ[ℚ, a, b]) = Ψ (m' : ℍ[ℚ, a, b]) := by rw [hκ m, hκ m', hκeq]

    by_contra hne
    have hne' : (m : ℍ[ℚ, a, b]) - (m' : ℍ[ℚ, a, b]) ≠ 0 := by
      intro h0; apply hne; exact Subtype.ext (sub_eq_zero.1 h0)
    obtain ⟨u, hu⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB _ hne'
    have h0 : Ψ ((m : ℍ[ℚ, a, b]) - (m' : ℍ[ℚ, a, b])) = 0 := by rw [map_sub, hΨeq, sub_self]
    have : (1 : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])]) = 0 := by
      rw [← map_one Ψ, ← u.mul_inv, map_mul, hu, h0, zero_mul]
    exact one_ne_zero this
  ·
    intro k α β
    obtain ⟨c, d, hcd⟩ := hdense k α
    obtain ⟨c', d', hcd'⟩ := hdense k β
    obtain ⟨y, hy⟩ : ∃ y : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])], y = combo θ ϖ (((c : ℤ) : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (((d : ℤ) : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v])
        (((c' : ℤ) : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (((d' : ℤ) : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) := ⟨_, rfl⟩
    have hyn : ‖nrd y‖ ≤ 1 := (horder y).2 ⟨_, _, _, _, hy⟩
    have hY : Θ.symm y ∈ Submodule.localBox Λ v := by
      have h1 : Θ.symm y ∈ {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ | ‖nrd (Θ x)‖ ≤ 1} := by
        show ‖nrd (Θ (Θ.symm y))‖ ≤ 1
        rw [RingEquiv.apply_symm_apply]; exact hyn
      rw [← hΘbox] at h1
      exact h1
    obtain ⟨z, hz, E, hE, hzE⟩ :=
      Submodule.exists_mem_add_one_tmul_pow_mul_of_mem_localBox Λ hO.fg hO.spanTop (Rat.HeightOneSpectrum.natGenerator v) hp v hpv k hY
    have hEbox : ‖nrd (Θ E)‖ ≤ 1 := by
      have h1 : E ∈ ((Submodule.localBox Λ v : AddSubgroup _) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) := hE
      rw [hΘbox] at h1
      exact h1
    obtain ⟨e₀, e₁, e₂, e₃, hEc0⟩ := (horder _).1 hEbox
    have hEc : Θ E = combo θ ϖ (e₀ : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (e₁ : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (e₂ : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) (e₃ : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) := hEc0
    have hΘpk : Θ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((Rat.HeightOneSpectrum.natGenerator v : v.adicCompletion ℚ) ^ k))
        = (((((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) ^ k : ℚ_[Rat.HeightOneSpectrum.natGenerator v])) : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])]) := by
      rw [hΘ1, map_pow, map_natCast, ← QuaternionAlgebra.coe_mul_eq_smul, mul_one]
      try rfl
    have hzy : Ψ z = combo θ ϖ
        ((((c : ℤ) : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) - (Rat.HeightOneSpectrum.natGenerator v : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) ^ k * e₀ : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v])
        ((((d : ℤ) : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) - (Rat.HeightOneSpectrum.natGenerator v : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) ^ k * e₁ : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v])
        ((((c' : ℤ) : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) - (Rat.HeightOneSpectrum.natGenerator v : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) ^ k * e₂ : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v])
        ((((d' : ℤ) : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) - (Rat.HeightOneSpectrum.natGenerator v : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) ^ k * e₃ : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) := by
      have h1 := congrArg Θ hzE
      rw [RingEquiv.apply_symm_apply, map_add, map_mul, hΘpk, hEc, coe_mul_combo, ← hΨ] at h1
      have h2 : Ψ z = y - combo θ ϖ ((((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) ^ k) * (e₀ : ℚ_[Rat.HeightOneSpectrum.natGenerator v])) ((((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) ^ k) * (e₁ : ℚ_[Rat.HeightOneSpectrum.natGenerator v]))
          ((((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) ^ k) * (e₂ : ℚ_[Rat.HeightOneSpectrum.natGenerator v])) ((((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) ^ k) * (e₃ : ℚ_[Rat.HeightOneSpectrum.natGenerator v])) := by
        rw [h1]; abel
      rw [h2, hy, combo_sub]
      push_cast
      ring_nf
    have hk := hκuniq ⟨z, hz⟩ _ _ _ _ hzy
    refine ⟨⟨z, hz⟩, ?_, ?_⟩
    · dsimp only
      rw [hk]; dsimp only
      have e : ι (((c : ℤ) : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) - (Rat.HeightOneSpectrum.natGenerator v : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) ^ k * e₀) + ι (((d : ℤ) : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) - (Rat.HeightOneSpectrum.natGenerator v : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) ^ k * e₁) * ω - α
          = -(α - (((c : ℤ) : CerednikDrinfeld.Zp2 (Rat.HeightOneSpectrum.natGenerator v)) + ((d : ℤ) : CerednikDrinfeld.Zp2 (Rat.HeightOneSpectrum.natGenerator v)) * ω))
            + ((Rat.HeightOneSpectrum.natGenerator v : CerednikDrinfeld.Zp2 (Rat.HeightOneSpectrum.natGenerator v))) ^ k * (-(ι e₀ + ι e₁ * ω)) := by
        simp only [map_sub, map_mul, map_pow, map_natCast, map_intCast]; ring
      rw [e]
      exact Ideal.add_mem _ ((Ideal.neg_mem_iff _).2 hcd) (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    · dsimp only
      rw [hk]; dsimp only
      have e : ι (((c' : ℤ) : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) - (Rat.HeightOneSpectrum.natGenerator v : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) ^ k * e₂) + ι (((d' : ℤ) : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) - (Rat.HeightOneSpectrum.natGenerator v : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) ^ k * e₃) * ω - β
          = -(β - (((c' : ℤ) : CerednikDrinfeld.Zp2 (Rat.HeightOneSpectrum.natGenerator v)) + ((d' : ℤ) : CerednikDrinfeld.Zp2 (Rat.HeightOneSpectrum.natGenerator v)) * ω))
            + ((Rat.HeightOneSpectrum.natGenerator v : CerednikDrinfeld.Zp2 (Rat.HeightOneSpectrum.natGenerator v))) ^ k * (-(ι e₂ + ι e₃ * ω)) := by
        simp only [map_sub, map_mul, map_pow, map_natCast, map_intCast]; ring
      rw [e]
      exact Ideal.add_mem _ ((Ideal.neg_mem_iff _).2 hcd') (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  ·
    intro m n₀ hmn
    have htrm : trd (m : ℍ[ℚ, a, b]) = (n₀ : ℚ) := by
      have h1 := add_star_eq_coe_trd (m : ℍ[ℚ, a, b])
      rw [hmn] at h1
      exact (QuaternionAlgebra.coe_injective h1).symm

    have hCH : ∀ x : ℍ[ℚ, a, b], Ψ x * Ψ x = ((((trd x : ℚ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v])) : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])]) * Ψ x - ((((nrd x : ℚ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v])) : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])]) := by
      intro x
      have := congrArg Ψ (sq_eq_trd_mul_sub_nrd x)
      rwa [map_mul, map_sub, map_mul, hΨcoe, hΨcoe] at this
    have htrnc : ∀ x : ℍ[ℚ, a, b], (∀ c : ℚ_[Rat.HeightOneSpectrum.natGenerator v], Ψ x ≠ (c : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])])) → trd (Ψ x) = ((trd x : ℚ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) :=
      fun x hx => (trd_eq_and_nrd_eq_of_sq_eq hD hx (hCH x)).1
    have hθnc : ∀ c : ℚ_[Rat.HeightOneSpectrum.natGenerator v], θ ≠ (c : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])]) := by
      intro c hc
      have h0 : combo θ ϖ (-c) 1 0 0 = 0 := by
        simp only [combo, hc, QuaternionAlgebra.coe_zero, zero_mul, add_zero, QuaternionAlgebra.coe_one, one_mul,
          QuaternionAlgebra.coe_neg, neg_add_cancel]
      exact one_ne_zero (hindep _ _ _ _ h0).2.1
    have htrΨ : ∀ x : ℍ[ℚ, a, b], trd (Ψ x) = ((trd x : ℚ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) := by
      intro x
      by_cases hc : ∃ c : ℚ_[Rat.HeightOneSpectrum.natGenerator v], Ψ x = (c : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])])
      · obtain ⟨c, hc⟩ := hc
        have hnc : ∀ c' : ℚ_[Rat.HeightOneSpectrum.natGenerator v], Ψ (x + θ₀) ≠ (c' : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])]) := by
          intro c' h'
          apply hθnc (c' - c)
          rw [map_add, hc] at h'
          change ((c : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])]) + θ = (c' : ℍ[ℚ_[Rat.HeightOneSpectrum.natGenerator v], (a : ℚ_[Rat.HeightOneSpectrum.natGenerator v]), (b : ℚ_[Rat.HeightOneSpectrum.natGenerator v])]) at h'
          rw [QuaternionAlgebra.coe_sub, ← h']
          abel
        have h1 := htrnc (x + θ₀) hnc
        rw [map_add, hc, trd_add', trd_coe', trd_add'] at h1
        change 2 * c + trd θ = (((trd x + trd θ₀ : ℚ)) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) at h1
        rw [htrθ, hθ₀t] at h1
        push_cast at h1
        rw [hc, trd_coe']
        linear_combination h1
      · push Not at hc
        exact htrnc x hc

    have h1 : trd (Ψ (m : ℍ[ℚ, a, b])) = 2 * ((κ m).1.1 : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) + ((t : ℤ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) * ((κ m).1.2 : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) := by
      rw [hκ m, trd_combo ((t : ℤ) : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) θ ϖ htrθ htrϖ htrθϖ]
    rw [htrΨ, htrm] at h1
    have h2 : ((κ m).1.1 + (κ m).1.1 + (t : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) * (κ m).1.2 : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) = (n₀ : ℤ_[Rat.HeightOneSpectrum.natGenerator v]) := by
      apply Subtype.ext
      push_cast
      push_cast at h1
      linear_combination (-1 : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) * h1
    have h3 := congrArg ι h2
    simp only [map_add, map_mul, map_intCast] at h3
    dsimp only
    rw [map_add, map_mul, hιfrob, hιfrob, hωfrob]
    linear_combination h3

end Main

end OrderCoord

end

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal in

open scoped Quaternion TensorProduct NumberField in
theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :
    ∃ coord : ↥Λ → Zp2 q × Zp2 q, IsOrderCoord Λ q coord := by
  obtain ⟨v, hv⟩ : ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), Rat.HeightOneSpectrum.natGenerator v = q :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, Fact.out⟩,
      congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨q, Fact.out⟩)⟩
  subst hv
  exact OrderCoord.main v hB Λ hΛ

end S_CerednikDrinfeld_QM_exists_isOrderCoord_of_isMaximalOrder
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_isOrderCoord_of_isMaximalOrder (solution)
