-- Prove2me | solution 1 for AvramDividend.Classical.bv_post_clock_positive_germ_of_dyadic_zero_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:09:16.113885+00:00
-- url     : https://prove2.me/submissions/cdf12aa1-07c4-4146-9b56-0e49b7af0cf7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_dyadic_slope_to_positive_right_germ_ws01c

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (τ : Ω → ℝ≥0) (δ : ℕ → ℝ≥0)
    (hδpos : ∀ n, 0 < δ n)
    (hRatio : ∀ n, (δ n : ℝ) ≤ 2 * (δ (n + 1) : ℝ))
    (hCover : ∀ (N : ℕ) (t : ℝ≥0), 0 < t → t < δ N →
      ∃ n : ℕ, N ≤ n ∧ δ (n + 1) ≤ t ∧ t ≤ δ n)
    (hSlope : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * (δ n : ℝ) -
          (X.X (τ ω + δ n) ω - X.X (τ ω) ω)) /
            (δ n : ℝ))
        atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P,
      ∃ ε : ℝ≥0, 0 < ε ∧
        ∀ t : ℝ≥0, 0 < t → t < ε →
          0 < X.X (τ ω + t) ω - X.X (τ ω) ω := by
  have hd : 0 < X.drift :=
    (bv_standing_drift_pos X hStanding hBV).1
  filter_upwards [bv_drift_deficit_ae_monotone_all_times X hBV,
    hSlope] with ω hMon hSlopeω
  let S₀ : ℝ≥0 → ℝ :=
    fun s => X.drift * (s : ℝ) - X.X s ω
  let S : ℝ≥0 → ℝ :=
    fun t => S₀ (τ ω + t) - S₀ (τ ω)
  have hSmon : Monotone S := by
    intro t u htu
    change S₀ (τ ω + t) - S₀ (τ ω) ≤
      S₀ (τ ω + u) - S₀ (τ ω)
    exact sub_le_sub_right
      (hMon (add_le_add_right htu (τ ω))) (S₀ (τ ω))
  have hIdentity (t : ℝ≥0) :
      S t = X.drift * (t : ℝ) -
        (X.X (τ ω + t) ω - X.X (τ ω) ω) := by
    dsimp [S, S₀]
    ring
  have hSlopeS :
      Tendsto (fun n : ℕ => S (δ n) / (δ n : ℝ))
        atTop (𝓝 (0 : ℝ)) := by
    have hEq :
        (fun n : ℕ => S (δ n) / (δ n : ℝ)) =
        (fun n : ℕ =>
          (X.drift * (δ n : ℝ) -
            (X.X (τ ω + δ n) ω - X.X (τ ω) ω)) /
              (δ n : ℝ)) := by
      funext n
      rw [hIdentity]
    rw [hEq]
    exact hSlopeω
  obtain ⟨ε, hεpos, hε⟩ :=
    bv_dyadic_slope_to_positive_right_germ_ws01c
      S δ X.drift hd hδpos hSmon hRatio hCover hSlopeS
  refine ⟨ε, hεpos, ?_⟩
  intro t ht hte
  have hPositive := hε t ht hte
  rw [hIdentity] at hPositive
  convert hPositive using 1 <;> ring
