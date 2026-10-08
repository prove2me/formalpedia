-- Prove2me | solution 1 for DatkoDelayWave.BoundaryDelay.no_accumulation_imaginary_axis
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:57:02.214103+00:00
-- url     : https://prove2.me/submissions/909ec49a-f205-4205-83a7-aebf1dfb57ab

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

set_option autoImplicit false

open DatkoDelayWave.BoundaryDelay in
theorem solution (a k ε : ℝ) (ha : 0 ≤ a) (hk : 0 < k)
    (hkK : k < (1 - K a) / (1 + K a)) (hε : 0 < ε) :
    ∃ β > (0 : ℝ), ∀ ω : ℂ, h a k ε ω = 0 → ω.re ≤ -β := by
  have hKpos : 0 < K a := Real.exp_pos _
  have h1K : 0 < 1 + K a := by linarith
  have hkK' : k * (1 + K a) < 1 - K a := by
    rw [lt_div_iff₀ h1K] at hkK; exact hkK
  have hK1 : K a < 1 := by nlinarith
  have hapos : 0 < a := by
    by_contra hc
    have ha0 : a = 0 := le_antisymm (not_lt.mp hc) ha
    have : K a = 1 := by simp [K, ha0]
    linarith
  let g : ℝ → ℝ := fun β =>
    1 - K a * Real.exp (2 * β) - k * Real.exp (ε * β) * (1 + K a * Real.exp (2 * β))
  have hgc : Continuous g := by fun_prop
  have hg0 : 0 < g 0 := by simp only [g, mul_zero, Real.exp_zero, mul_one]; linarith
  have hev : ∀ᶠ β in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < g β ∧ β < a / 2 ∧ 0 < β := by
    refine Filter.Eventually.and ?_ (Filter.Eventually.and ?_ self_mem_nhdsWithin)
    · exact nhdsWithin_le_nhds (hgc.continuousAt.eventually (lt_mem_nhds hg0))
    · exact nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
  obtain ⟨β, hgβ, hβa, hβ⟩ := hev.exists
  refine ⟨β, hβ, fun ω hω => ?_⟩
  by_contra hre
  rw [not_le] at hre
  unfold h f at hω
  have hid : ((ω + (a:ℂ)) * (1 + (K a : ℂ) * Complex.exp (-2 * ω))) =
      -((k:ℂ) * ω * Complex.exp (-(ε : ℂ) * ω) * (1 - (K a : ℂ) * Complex.exp (-2 * ω))) := by
    linear_combination hω
  have hEn : ‖Complex.exp (-2 * ω)‖ ≤ Real.exp (2 * β) := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; linarith
  have hWn : ‖Complex.exp (-(ε : ℂ) * ω)‖ ≤ Real.exp (ε * β) := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; nlinarith
  set E := Complex.exp (-2 * ω) with hE
  set W := Complex.exp (-(ε:ℂ) * ω) with hW
  set q := K a * Real.exp (2 * β) with hq
  have hKE : ‖(K a : ℂ) * E‖ ≤ q := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hKpos]
    exact mul_le_mul_of_nonneg_left hEn hKpos.le
  have hexpε : 0 < Real.exp (ε * β) := Real.exp_pos _
  have hq0 : 0 ≤ q := by positivity
  have hgβ' : k * Real.exp (ε * β) * (1 + q) < 1 - q := by
    simp only [g] at hgβ; linarith
  have hA : 1 - q ≤ ‖1 + (K a : ℂ) * E‖ := by
    have := norm_add_le (1 + (K a:ℂ) * E) (-((K a:ℂ) * E))
    simp only [add_neg_cancel_right, norm_neg, norm_one] at this
    linarith
  have hB : ‖1 - (K a : ℂ) * E‖ ≤ 1 + q := by
    have := norm_sub_le (1 : ℂ) ((K a:ℂ) * E)
    rw [norm_one] at this
    linarith
  have hnorm : ‖ω + (a:ℂ)‖ * ‖1 + (K a : ℂ) * E‖ = k * ‖ω‖ * ‖W‖ * ‖1 - (K a : ℂ) * E‖ := by
    have := congrArg norm hid
    simpa [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk] using this
  have hre' : (ω + (a:ℂ)).re = ω.re + a := by simp
  have him' : (ω + (a:ℂ)).im = ω.im := by simp
  have hNpos : 0 < ‖ω + (a:ℂ)‖ := by
    have := Complex.abs_re_le_norm (ω + (a:ℂ))
    rw [hre', abs_of_pos (by linarith)] at this
    linarith
  have hMN : ‖ω‖ ≤ ‖ω + (a:ℂ)‖ := by
    have h1 := Complex.sq_norm ω
    have h2 := Complex.sq_norm (ω + (a:ℂ))
    rw [Complex.normSq_apply] at h1 h2
    rw [hre', him'] at h2
    have hsq : ‖ω‖ ^ 2 ≤ ‖ω + (a:ℂ)‖ ^ 2 := by rw [h1, h2]; nlinarith
    nlinarith [norm_nonneg ω, norm_nonneg (ω + (a:ℂ))]
  have hWn0 : 0 ≤ ‖W‖ := norm_nonneg _
  have hB0 : 0 ≤ ‖1 - (K a : ℂ) * E‖ := norm_nonneg _
  have step1 : ‖ω + (a:ℂ)‖ * (1 - q) ≤ ‖ω + (a:ℂ)‖ * ‖1 + (K a : ℂ) * E‖ :=
    mul_le_mul_of_nonneg_left hA hNpos.le
  have step2 : k * ‖ω‖ * ‖W‖ * ‖1 - (K a : ℂ) * E‖
      ≤ k * ‖ω + (a:ℂ)‖ * Real.exp (ε * β) * (1 + q) := by
    have e1 : k * ‖ω‖ ≤ k * ‖ω + (a:ℂ)‖ := mul_le_mul_of_nonneg_left hMN hk.le
    have e2 : k * ‖ω‖ * ‖W‖ ≤ k * ‖ω + (a:ℂ)‖ * Real.exp (ε * β) :=
      mul_le_mul e1 hWn hWn0 (by positivity)
    exact mul_le_mul e2 hB hB0 (by positivity)
  have step3 : k * ‖ω + (a:ℂ)‖ * Real.exp (ε * β) * (1 + q)
      < ‖ω + (a:ℂ)‖ * (1 - q) := by
    have := mul_lt_mul_of_pos_left hgβ' hNpos
    nlinarith
  linarith
