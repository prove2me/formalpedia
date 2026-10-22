-- Prove2me | solution 1 for CVPricing.CertEquiv.ls_representation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:39:43.918462+00:00
-- url     : https://prove2.me/submissions/905e2cb4-eff6-4ce3-8b11-d4e359437f9c

import Mathlib
import Definitions.Def_CVPricing_CertEquiv_EventA

set_option autoImplicit false
open KeskinZeevi.SufficientConditions CVPricing.CertEquiv Matrix

theorem solution (a₀ a₁ : ℝ) (p e : ℕ → ℝ) (hp : p 1 ≠ p 2) {t : ℕ} (ht : 2 ≤ t) :
    lsEstimateOf p (fun s => a₀ + a₁ * p s + e s) t =
      (a₀ + (avgPriceOf e t - avgPriceOf p t * crossSum p e t / infoMetricOf p t),
        a₁ + crossSum p e t / infoMetricOf p t) := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hcard : ((Finset.Icc 1 t).card : ℝ) = t := by simp
  set S1 : ℝ := ∑ s ∈ Finset.Icc 1 t, p s with hS1
  set S2 : ℝ := ∑ s ∈ Finset.Icc 1 t, p s ^ 2 with hS2
  set E1 : ℝ := ∑ s ∈ Finset.Icc 1 t, e s with hE1
  set SpE : ℝ := ∑ s ∈ Finset.Icc 1 t, p s * e s with hSpE
  have hpbar : avgPriceOf p t = S1 / t := rfl
  have hebar : avgPriceOf e t = E1 / t := rfl
  have key : ∀ c : ℝ, ∑ s ∈ Finset.Icc 1 t, (p s - c) ^ 2 = S2 - 2 * c * S1 + t * c ^ 2 := by
    intro c
    have h : ∀ s, (p s - c) ^ 2 = p s ^ 2 - 2 * c * p s + c ^ 2 := fun s => by ring
    simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, hcard]
    rfl
  have hV : infoMetricOf p t = S2 - S1 ^ 2 / t := by
    unfold infoMetricOf
    rw [hpbar, key]
    field_simp
    ring
  have hC : crossSum p e t = SpE - S1 / t * E1 := by
    unfold crossSum
    rw [hpbar]
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  have hVpos : 0 < infoMetricOf p t := by
    unfold infoMetricOf
    have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 t := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]; omega
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun s => (p s - avgPriceOf p t) ^ 2) (fun i _ _ => sq_nonneg _)
    rw [Finset.sum_pair (by norm_num)] at h1
    have : 0 < (p 1 - avgPriceOf p t) ^ 2 + (p 2 - avgPriceOf p t) ^ 2 := by
      by_contra hcon
      push_neg at hcon
      have a1 : (p 1 - avgPriceOf p t) ^ 2 = 0 := by nlinarith [sq_nonneg (p 1 - avgPriceOf p t), sq_nonneg (p 2 - avgPriceOf p t)]
      have a2 : (p 2 - avgPriceOf p t) ^ 2 = 0 := by nlinarith [sq_nonneg (p 1 - avgPriceOf p t), sq_nonneg (p 2 - avgPriceOf p t)]
      have b1 := pow_eq_zero_iff (two_ne_zero) |>.1 a1
      have b2 := pow_eq_zero_iff (two_ne_zero) |>.1 a2
      exact hp (by linarith)
    linarith
  set V := infoMetricOf p t with hVdef
  have hVne : V ≠ 0 := hVpos.ne'
  have hJ : fisherOf p t = !![(t : ℝ), S1; S1, S2] := by
    unfold fisherOf
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.sum_apply, hS1, hS2, hcard]
  have hdet : (fisherOf p t).det = t * V := by
    rw [hJ, Matrix.det_fin_two_of, hV]
    field_simp
  have hdetU : IsUnit (fisherOf p t).det := by
    rw [hdet]; exact IsUnit.mk0 _ (mul_ne_zero htpos.ne' hVne)
  have hD0 : ∑ s ∈ Finset.Icc 1 t, (a₀ + a₁ * p s + e s) = t * a₀ + a₁ * S1 + E1 := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcard]
    rfl
  have hD1 : ∑ s ∈ Finset.Icc 1 t, (a₀ + a₁ * p s + e s) * p s = a₀ * S1 + a₁ * S2 + SpE := by
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hS1, hS2, hSpE, mul_assoc, pow_two, mul_comm (e _) (p _)]
  unfold lsEstimateOf
  simp only
  rw [hD0, hD1]
  set q : ℝ := crossSum p e t / V with hqdef
  have hq : q * V = crossSum p e t := div_mul_cancel₀ _ hVne
  have hq' : q * (S2 - S1 ^ 2 / t) = SpE - S1 / t * E1 := by rw [← hV, hq, hC]
  set w : Fin 2 → ℝ := ![a₀ + (E1 / t - S1 / t * q), a₁ + q] with hw
  have hJw : (fisherOf p t) *ᵥ w = ![t * a₀ + a₁ * S1 + E1, a₀ * S1 + a₁ * S2 + SpE] := by
    rw [hJ]
    ext i
    fin_cases i
    · simp [hw, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
      ring
    · simp [hw, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination hq'
  have : (fisherOf p t)⁻¹ *ᵥ ![t * a₀ + a₁ * S1 + E1, a₀ * S1 + a₁ * S2 + SpE] = w := by
    rw [← hJw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetU, Matrix.one_mulVec]
  rw [this]
  have h2 : avgPriceOf p t * crossSum p e t / V = S1 / t * q := by
    rw [hpbar, hqdef]; ring
  rw [h2, hebar]
  simp [hw]
