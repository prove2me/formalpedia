-- Prove2me | solution 1 for CliffordTApprox.Ancilla.norm_deficit
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:23:02.416099+00:00
-- url     : https://prove2.me/submissions/1e342666-ab2d-40b0-bdde-813987a85f58

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

namespace Aux_CTAnd
open CliffordTApprox.Ancilla

theorem rerr (k : ℕ) (φ : ℝ) (hφ₀ : 0 ≤ φ) (hφ₁ : φ ≤ Real.pi / 4) :
    ‖gammaApprox k φ - Complex.exp (φ * Complex.I)‖ ≤ Real.sqrt 2 / 2 ^ k := by
  set u : ℝ := (roundX k φ : ℝ) - 2 ^ k * Real.cos φ with hu
  set v : ℝ := (roundY k φ : ℝ) - 2 ^ k * Real.sin φ with hv
  have hu1 : u ^ 2 ≤ 1 := by
    have h1 := Int.floor_le ((2 : ℝ) ^ k * Real.cos φ)
    have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ k * Real.cos φ)
    have : u ≤ 0 := by rw [hu]; unfold roundX; linarith
    have : -1 < u := by rw [hu]; unfold roundX; linarith
    nlinarith
  have hv1 : v ^ 2 ≤ 1 := by
    have h1 := Int.floor_le ((2 : ℝ) ^ k * Real.sin φ)
    have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ k * Real.sin φ)
    have : v ≤ 0 := by rw [hv]; unfold roundY; linarith
    have : -1 < v := by rw [hv]; unfold roundY; linarith
    nlinarith
  have hexp : Complex.exp (φ * Complex.I) = (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have h2k : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have key : gammaApprox k φ - Complex.exp (φ * Complex.I)
      = ((u : ℂ) + (v : ℂ) * Complex.I) / (2 : ℂ) ^ k := by
    unfold gammaApprox
    rw [hexp, hu, hv]
    push_cast
    field_simp
    ring
  rw [key, norm_div, Complex.norm_add_mul_I, norm_pow]
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [hn2]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.sqrt_le_sqrt
  linarith

lemma normg (k : ℕ) (φ : ℝ) :
    ‖gammaApprox k φ‖ = Real.sqrt ((roundX k φ : ℝ) ^ 2 + (roundY k φ : ℝ) ^ 2) / 2 ^ k := by
  have e : gammaApprox k φ
      = (((roundX k φ : ℝ) : ℂ) + ((roundY k φ : ℝ) : ℂ) * Complex.I) / (2 : ℂ) ^ k := by
    unfold gammaApprox; push_cast; rfl
  rw [e, norm_div, Complex.norm_add_mul_I, norm_pow]
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [hn2]

lemma normg_sq (k : ℕ) (φ : ℝ) :
    ‖gammaApprox k φ‖ ^ 2 = ((roundX k φ : ℝ) ^ 2 + (roundY k φ : ℝ) ^ 2) / 4 ^ k := by
  rw [normg, div_pow, Real.sq_sqrt (by positivity)]
  congr 1
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

end Aux_CTAnd

open CliffordTApprox.Ancilla in
theorem solution (k : ℕ) (φ : ℝ) (hφ₀ : 0 ≤ φ) (hφ₁ : φ ≤ Real.pi / 4) :
    ‖gammaApprox k φ‖ ≤ 1 ∧
    1 - ‖gammaApprox k φ‖ ^ 2 ≤ 2 * Real.sqrt 2 / 2 ^ k ∧
    ∀ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = deficit k φ →
      ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℤ) : ℝ) / 4 ^ k = 1 - ‖gammaApprox k φ‖ ^ 2 := by
  have hpi : φ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hcos : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hpi⟩
  have hsin : 0 ≤ Real.sin φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hφ₀ (by linarith [Real.pi_pos])
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have h4k : (4 : ℝ) ^ k = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hX0 : (0 : ℝ) ≤ roundX k φ := by
    unfold roundX; exact_mod_cast Int.floor_nonneg.mpr (by positivity)
  have hY0 : (0 : ℝ) ≤ roundY k φ := by
    unfold roundY; exact_mod_cast Int.floor_nonneg.mpr (by positivity)
  have hX1 : (roundX k φ : ℝ) ≤ 2 ^ k * Real.cos φ := by unfold roundX; exact Int.floor_le _
  have hY1 : (roundY k φ : ℝ) ≤ 2 ^ k * Real.sin φ := by unfold roundY; exact Int.floor_le _
  have hsc := Real.sin_sq_add_cos_sq φ
  have hsq : (roundX k φ : ℝ) ^ 2 + (roundY k φ : ℝ) ^ 2 ≤ 4 ^ k := by
    rw [h4k]
    have := mul_le_mul hX1 hX1 hX0 (by positivity)
    have := mul_le_mul hY1 hY1 hY0 (by positivity)
    nlinarith
  have hg2 : ‖gammaApprox k φ‖ ^ 2 ≤ 1 := by
    rw [Aux_CTAnd.normg_sq, div_le_one (by positivity)]; exact hsq
  have hg1 : ‖gammaApprox k φ‖ ≤ 1 := by
    have := norm_nonneg (gammaApprox k φ)
    nlinarith
  refine ⟨hg1, ?_, ?_⟩
  · have he : ‖Complex.exp (φ * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I φ
    have hr := Aux_CTAnd.rerr k φ hφ₀ hφ₁
    have htri : ‖Complex.exp (φ * Complex.I)‖ - ‖gammaApprox k φ‖
        ≤ ‖gammaApprox k φ - Complex.exp (φ * Complex.I)‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le _ _
    rw [he] at htri
    have hn := norm_nonneg (gammaApprox k φ)
    have h1 : 1 - ‖gammaApprox k φ‖ ≤ Real.sqrt 2 / 2 ^ k := htri.trans hr
    have h0 : 0 ≤ 1 - ‖gammaApprox k φ‖ := by linarith
    have hs : 0 ≤ Real.sqrt 2 / 2 ^ k := by positivity
    have e2 : 1 - ‖gammaApprox k φ‖ ^ 2
        = (1 - ‖gammaApprox k φ‖) * (1 + ‖gammaApprox k φ‖) := by ring
    rw [e2, mul_div_assoc]
    nlinarith
  · intro a b c d habcd
    rw [habcd, Aux_CTAnd.normg_sq]
    unfold deficit
    push_cast
    field_simp
    ring
