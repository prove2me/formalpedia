-- Prove2me | solution 1 for DeletedPrimes.smooth_half_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:22:04.390982+00:00
-- url     : https://prove2.me/submissions/7dbcf74a-ed46-4324-9328-7e7c74e462a8

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Smooth
import Theorems.Thm_DeletedPrimes_le_of_frequently_rpow_le
import Theorems.Thm_DeletedPrimes_theta_set_one_mem


set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} {α δ : ℝ} (hδα : δ < α / 2)
    (hcount : ∀ θ σ : ℝ, 0 ≤ θ → IsRegular S θ → max θ δ < σ →
      ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X → (intervalCount S X : ℝ) ≤ C * X ^ (2 * σ) * Real.log X ^ 2)
    (hlower : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, c * X ^ α / Real.log X ≤ intervalCount S X) :
    α / 2 ≤ theta S := by
  obtain ⟨c, hc, hev⟩ := hlower
  refine le_csInf ⟨1, theta_set_one_mem S⟩ fun θ hθ => ?_
  obtain ⟨hθ0, hθreg⟩ := hθ
  by_contra hlt
  push Not at hlt
  have hmax : max θ δ < α / 2 := max_lt hlt hδα
  set σ := (max θ δ + α / 2) / 2 with hσ
  have hσ1 : max θ δ < σ := by rw [hσ]; linarith
  have hσ2 : 2 * σ < α := by rw [hσ]; linarith
  obtain ⟨C, hC⟩ := hcount θ σ hθ0 hθreg hσ1
  set ε := (α - 2 * σ) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hlog : ∀ᶠ X : ℝ in atTop, ‖Real.log X ^ (3 : ℝ)‖ ≤ 1 * ‖X ^ ε‖ :=
    (isLittleO_log_rpow_rpow_atTop 3 hε0).bound one_pos
  have key : ∀ᶠ X : ℝ in atTop, c * X ^ α ≤ |C| * X ^ (2 * σ + ε) := by
    filter_upwards [hev, hlog, eventually_ge_atTop (2 : ℝ)] with X h1 h2 h3
    have hX0 : 0 < X := by linarith
    have hL : 0 < Real.log X := Real.log_pos (by linarith)
    have h4 := hC X h3
    have hL3 : Real.log X ^ 3 ≤ X ^ ε := by
      have e1 : Real.log X ^ (3 : ℝ) = Real.log X ^ (3 : ℕ) := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [e1, Real.norm_of_nonneg (by positivity), one_mul, Real.norm_of_nonneg (by positivity)] at h2
      exact h2
    have h5 : c * X ^ α ≤ C * X ^ (2 * σ) * Real.log X ^ 3 := by
      have h' : c * X ^ α / Real.log X ≤ C * X ^ (2 * σ) * Real.log X ^ 2 := le_trans h1 h4
      rw [div_le_iff₀ hL] at h'
      calc c * X ^ α ≤ C * X ^ (2 * σ) * Real.log X ^ 2 * Real.log X := h'
        _ = C * X ^ (2 * σ) * Real.log X ^ 3 := by ring
    have h6 : C * X ^ (2 * σ) * Real.log X ^ 3 ≤ |C| * X ^ (2 * σ) * Real.log X ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have h7 : |C| * X ^ (2 * σ) * Real.log X ^ 3 ≤ |C| * X ^ (2 * σ) * X ^ ε :=
      mul_le_mul_of_nonneg_left hL3 (by positivity)
    rw [Real.rpow_add hX0, ← mul_assoc]
    linarith
  have := le_of_frequently_rpow_le hc key.frequently
  rw [hε] at this
  linarith
end DeletedPrimes
