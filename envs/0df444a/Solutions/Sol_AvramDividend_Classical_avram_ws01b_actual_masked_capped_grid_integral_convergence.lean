-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_actual_masked_capped_grid_integral_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T12:52:08.193878+00:00
-- url     : https://prove2.me/submissions/7edbfc72-a071-4440-884f-1e5a5a5a660f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat03_bounded_grid_l2_unconditional
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Original-Lévy killed-grid expectations converge from integrable stopped rewards and genuine L² domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (clock : ℕ → ℕ → ℝ≥0) (hc : ∀ n, Monotone (clock n))
    (hc0 : ∀ n, clock n 0 = 0)
    (H : ℕ → Filtration ℕ mΩ) (hH : ∀ n k, H n k = 𝓕 (clock n k))
    (lower upper : ℝ) (m : ℕ → ℕ) (K : ℕ → Ω → ℕ)
    (hK : ∀ n ω, K n ω = hittingBtwn
      (fun k ξ => max (X.X (clock n k) ξ - upper)
        (lower - X.X (clock n k) ξ)) (Set.Ioi (0 : ℝ)) 0 (m n) ω)
    (N : ℝ≥0) (hNm : ∀ n, clock n (m n) ≤ N)
    (S : ℕ → Set Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n ω, Y n ω = (S n).indicator
      (fun η => Real.exp (-(q * (clock n (K n η) : ℝ))) *
        W (x + X.X (clock n (K n η)) η)) ω)
    (hYi : ∀ n, Integrable (Y n) P)
    (hY0 : ∀ n ω, 0 ≤ Y n ω)
    (Z : Ω → ℝ)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (𝓝 (∫ ω, Z ω ∂P)) := by
  let R : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (-(q * (clock n (K n ω) : ℝ))) *
      W (x + X.X (clock n (K n ω)) ω)
  let C : ℝ := ((X.ψ θ - q)⁻¹)^2 *
    Real.exp (2 * θ * (x + 1) + (N : ℝ) * max (X.ψ (2 * θ)) 0)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hSqLe (n : ℕ) (ω : Ω) : (Y n ω)^2 ≤ (R n ω)^2 := by
    have hy : Y n ω = (S n).indicator (R n) ω := hY n ω
    rw [hy]
    by_cases h : ω ∈ S n
    · simp only [Set.indicator_of_mem h, le_refl]
    · simpa [Set.indicator_of_notMem h] using sq_nonneg (R n ω)
  have hY2 (n : ℕ) : Integrable (fun ω => (Y n ω)^2) P ∧
      (∫ ω, (Y n ω)^2 ∂P) ≤ C := by
    have hOrig := chat03_bounded_grid_l2_unconditional
      X q hq W hW θ x hθ hψ (clock n) (hc n) (hc0 n)
        (H n) (hH n) lower upper (m n) (K n) (hK n) N (hNm n)
    have hOrigR : Integrable (fun ω => (R n ω)^2) P ∧
        (∫ ω, (R n ω)^2 ∂P) ≤ C := by
      simpa only [R, C] using hOrig
    have hNorm : ∀ᵐ ω ∂P, ‖(Y n ω)^2‖ ≤ ‖(R n ω)^2‖ := by
      filter_upwards with ω
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (Y n ω)),
        abs_of_nonneg (sq_nonneg (R n ω))] using hSqLe n ω
    have hInt : Integrable (fun ω => (Y n ω)^2) P :=
      hOrigR.1.mono ((hYi n).aestronglyMeasurable.pow 2) hNorm
    exact ⟨hInt, le_trans
      (integral_mono hInt hOrigR.1 (fun ω => hSqLe n ω)) hOrigR.2⟩
  have hZm : AEStronglyMeasurable Z P :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hYi n).aestronglyMeasurable) hconv
  exact nonnegative_integral_tendsto_of_uniform_second_moment Y Z
    (fun n => (hYi n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (hY0 n))
    hZm hconv C hC hY2
