-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_two_sided_grid_indicated_scale_l2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:31:15.922433+00:00
-- url     : https://prove2.me/submissions/6e168d2c-9162-4b64-a517-440d78cf5579

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_two_sided_grid_source_scale_l2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The source grid scale-square bound survives restricting the reward
to any measurable survival-history event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω)
    (N : ℝ≥0) (hN : ∀ ω, clock (K ω) ≤ N)
    (hMeas : AEStronglyMeasurable (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) P)
    (B : Set Ω) (hB : MeasurableSet B) :
    Integrable (B.indicator (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2)) P ∧
    (∫ ω, B.indicator (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) ω ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by
  obtain ⟨hInt, hBound⟩ :=
    avram_root29_01_two_sided_grid_source_scale_l2
      X q hq W hW θ x hθ hψ clock hc hc0 H hH
      lower upper m K hK N hN hMeas
  have hIndInt : Integrable (B.indicator (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2)) P :=
    hInt.indicator hB
  refine ⟨hIndInt, ?_⟩
  have hPoint (ω : Ω) :
      B.indicator (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) ω ≤
        (Real.exp (-(q * (clock (K ω) : ℝ))) *
          W (x + X.X (clock (K ω)) ω)) ^ 2 := by
    by_cases hω : ω ∈ B
    · simp only [Set.indicator_of_mem hω, le_refl]
    · simp only [Set.indicator_of_notMem hω]
      exact sq_nonneg _
  exact (integral_mono hIndInt hInt hPoint).trans hBound
