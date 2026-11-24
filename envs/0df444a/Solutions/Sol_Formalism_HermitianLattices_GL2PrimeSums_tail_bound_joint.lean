-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.tail_bound_joint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:53.622492+00:00
-- url     : https://prove2.me/submissions/31b26f89-9a60-4106-b9b7-d61a7ae12827

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpNegLeDivPowFour
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_tail_main
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_pointwise
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_bound1
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_bound2
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_ev_small

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums
open TailSumsHookFormulaTorsion
namespace Formalism.HermitianLattices.GL2PrimeSums
theorem _root_.solution : TailSumBound := by
  intro ε hε hε1 C₁ c₁ CM hC₁ hc₁ hCM
  obtain ⟨L₀, hL₀⟩ := ev_small (6 / ε) C₁ c₁ hc₁
  set κ : ℝ := 1600 / ε + 1 with hκ
  set K₂ : ℝ := 4 * C₁ * (804 * κ ^ 2 + 5000000000) with hK₂
  have ev1 : ∀ᶠ x : ℝ in atTop, max L₀ 3 ≤ x ^ (ε / 6) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have ev2 : ∀ᶠ x : ℝ in atTop, K₂ ≤ x ^ (ε / 2) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp ((ev1.and ev2).and (eventually_ge_atTop (3 : ℝ)))
  refine ⟨x₀, C₁ * (804 * 802 ^ 2 + 5000000000) + 2 + CM + 200, ?_⟩
  intro x hx Q hQ hLlo hLhi a S hS hMert H1 H2
  obtain ⟨⟨h1, h2⟩, hx3⟩ := hx₀ x hx
  set L := Real.log Q with hLdef
  have hx0 : 0 < x := by linarith
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans (h1.trans hLlo)
  have hL3 : 3 ≤ L := (le_max_right _ _).trans (h1.trans hLlo)
  have hL0 : 0 < L := by linarith
  have hQ1 : 1 ≤ Q := by
    by_contra h
    rw [not_le] at h
    have := Real.log_nonpos hQ.le h.le
    linarith
  set E := C₁ * (4 * L ^ 8 * Real.exp (-L) + 384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * L))) with hE
  have hE0 : 0 ≤ E := by positivity
  have hxL : x ≤ L ^ (6 / ε) := by
    have h : (x ^ (ε / 6)) ^ (6 / ε) ≤ L ^ (6 / ε) :=
      Real.rpow_le_rpow (by positivity) hLlo (by positivity)
    rwa [← Real.rpow_mul hx0.le, show ε / 6 * (6 / ε) = 1 by field_simp, Real.rpow_one] at h
  have hxE : x * E ≤ 1 / 6 := (mul_le_mul_of_nonneg_right hxL hE0).trans (hL₀ L hLL₀)
  have hE6 : E ≤ 1 / 6 := by
    have h : 1 * E ≤ x * E := mul_le_mul_of_nonneg_right (by linarith) hE0
    linarith
  have hpw : ∀ n : ℕ, 3 ≤ n → ‖∑ k ∈ Icc 1 n, a k‖ ≤
      n * (C₁ * ((n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2) + E * (1 / Real.log (n : ℝ) ^ 2)) :=
    fun n hn => pointwise a Q C₁ c₁ hC₁ hc₁ hQ (by linarith) H1 H2 n hn
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_three]
  constructor
  · obtain ⟨hM3, hMp, hl0, hl1⟩ := bound1 x Q hx3 hQ1
    have T := tail_main a S hS _ hM3 Q hQ1 C₁ E hC₁.le hE0 (fun n hn => hpw n (hM3.trans hn))
    set M := ⌊x ^ (400 : ℝ)⌋₊
    set y := x ^ (ε / 4) with hy
    have hy1 : 1 ≤ y := Real.one_le_rpow (by linarith) (by positivity)
    have hy2 : y ^ 2 = x ^ (ε / 2) := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
    have hy4 : y ^ 4 = x ^ ε := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
    have hlx : Real.log x ≤ y / (ε / 4) := Real.log_le_rpow_div hx0.le (by positivity)
    have hl2 : Real.log (M * Q) ≤ κ * y := by
      have e : 400 * (y / (ε / 4)) + y = κ * y := by rw [hκ]; field_simp; ring
      linarith
    have hl3 : Real.log (M * Q) ^ 2 ≤ κ ^ 2 * y ^ 2 := by
      have h := pow_le_pow_left₀ hl0 hl2 2
      rwa [mul_pow] at h
    have hyy : 1 ≤ y ^ 2 := one_le_pow₀ hy1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le, ← hy4]
    have s1 : (804 * Real.log (M * Q) ^ 2 + 5000000000) * (M : ℝ) ^ (-((1 : ℝ) / 400)) ≤
        ((804 * κ ^ 2 + 5000000000) * y ^ 2) * (2 / x) := by
      apply mul_le_mul _ hMp (by positivity) (by positivity)
      linarith
    have s2 : x * ‖S - ∑ n ∈ Icc 1 M, a n / (n : ℂ)‖ ≤
        x * (C₁ * (((804 * κ ^ 2 + 5000000000) * y ^ 2) * (2 / x)) + 3 * E) := by
      apply mul_le_mul_of_nonneg_left _ hx0.le
      have := mul_le_mul_of_nonneg_left s1 hC₁.le
      linarith
    have s3 : x * (C₁ * (((804 * κ ^ 2 + 5000000000) * y ^ 2) * (2 / x)) + 3 * E) =
        K₂ / 2 * y ^ 2 + 3 * (x * E) := by
      rw [hK₂]; field_simp; ring
    have s4 : K₂ * y ^ 2 ≤ y ^ 2 * y ^ 2 := by
      rw [← hy2] at h2
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have s5 : 1 ≤ y ^ 2 * y ^ 2 := one_le_mul_of_one_le_of_one_le hyy hyy
    have s6 : y ^ 4 = y ^ 2 * y ^ 2 := by ring
    rw [s6]
    linarith
  · obtain ⟨hM3, hMp, hlM⟩ := bound2 L hL3
    have T := tail_main a S hS _ hM3 Q hQ1 C₁ E hC₁.le hE0 (fun n hn => hpw n (hM3.trans hn))
    set M := ⌈L ^ 800⌉₊
    have hM3' : (3 : ℝ) ≤ M := by exact_mod_cast hM3
    have hM0 : (0 : ℝ) < M := by linarith
    have hlogL : Real.log L ≤ L := by
      have := Real.log_le_sub_one_of_pos hL0
      linarith
    have hl : Real.log (M * Q) = Real.log (M : ℝ) + L := Real.log_mul hM0.ne' hQ.ne'
    have hl0 : 0 ≤ Real.log (M * Q) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by linarith) hQ1)
    have hl2 : Real.log (M * Q) ≤ 802 * L := by linarith
    have hl3 : Real.log (M * Q) ^ 2 ≤ 802 ^ 2 * L ^ 2 := by
      have h := pow_le_pow_left₀ hl0 hl2 2
      rwa [mul_pow] at h
    have hLL : 1 ≤ L ^ 2 := one_le_pow₀ (by linarith)
    have s1 : (804 * Real.log (M * Q) ^ 2 + 5000000000) * (M : ℝ) ^ (-((1 : ℝ) / 400)) ≤
        804 * 802 ^ 2 + 5000000000 := by
      calc _ ≤ ((804 * 802 ^ 2 + 5000000000) * L ^ 2) * (1 / L ^ 2) := by
            apply mul_le_mul _ hMp (by positivity) (by positivity)
            linarith
        _ = _ := by field_simp
    have s2 : ‖∑ n ∈ Icc 1 M, a n / (n : ℂ)‖ ≤ Real.log (M : ℝ) + CM := by
      have h := hMert M (by linarith)
      rw [Nat.floor_natCast] at h
      refine (norm_sum_le _ _).trans (le_trans (le_of_eq ?_) h)
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [norm_div, Complex.norm_natCast]
    have s3 : Real.log L ≤ ε / 4 * Real.log x := by
      have h := Real.log_le_log hL0 hLhi
      rwa [Real.log_rpow hx0] at h
    have s4 : ‖S‖ ≤ ‖S - ∑ n ∈ Icc 1 M, a n / (n : ℂ)‖ + ‖∑ n ∈ Icc 1 M, a n / (n : ℂ)‖ := by
      have h := norm_add_le (S - ∑ n ∈ Icc 1 M, a n / (n : ℂ)) (∑ n ∈ Icc 1 M, a n / (n : ℂ))
      simpa using h
    have s5 : ε * Real.log x ≤ Real.log x := by
      have h := mul_le_mul_of_nonneg_right hε1.le (by linarith : 0 ≤ Real.log x)
      linarith
    have s6 := mul_le_mul_of_nonneg_left s1 hC₁.le
    have s7 : (C₁ * (804 * 802 ^ 2 + 5000000000) + 2 + CM) * 1 ≤
        (C₁ * (804 * 802 ^ 2 + 5000000000) + 2 + CM) * Real.log x :=
      mul_le_mul_of_nonneg_left hlogx (by positivity)
    linarith
end Formalism.HermitianLattices.GL2PrimeSums
