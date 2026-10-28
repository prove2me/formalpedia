-- Prove2me | solution 1 for AvramDividend.Classical.esscher_finite_grid_stop_likelihood_l2_seminorm_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:42:12.64789+00:00
-- url     : https://prove2.me/submissions/11ab0c45-b178-4c51-b516-9b2ab264c25f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_l2_lintegral_bound

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (hbound : ∀ ω, τ ω ≤ H) :
    eLpNorm (fun ω => Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ)) (2 : ℝ≥0∞) P ≤
    ENNReal.ofReal (Real.exp
      (((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|) / 2)) := by
  have hL := AvramDividend.Classical.esscher_finite_grid_stop_likelihood_l2_lintegral_bound
    X θ hθ T H τ grid hgrid hT hstop hbound
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  have hsq : ∀ ω, ‖Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)‖ₑ ^ ((2 : ℝ≥0∞).toReal)
      = ENNReal.ofReal (Real.exp ((2 * θ) * X.X (τ ω) ω - 2 * (τ ω : ℝ) * X.ψ θ)) := by
    intro ω
    rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofNat,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num)]
    congr 1
    rw [← Real.exp_mul]; congr 1; ring
  simp_rw [hsq]
  have h2 : (1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
  rw [h2]
  calc (∫⁻ ω, ENNReal.ofReal (Real.exp ((2 * θ) * X.X (τ ω) ω - 2 * (τ ω : ℝ) * X.ψ θ)) ∂P)
        ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hL (by norm_num)
    _ = ENNReal.ofReal (Real.exp (((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|) / 2)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
        congr 2; ring
