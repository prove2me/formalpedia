-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_post_clock_positive_germ_of_dyadic_zero_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T14:27:53.400796+00:00
-- url     : https://prove2.me/submissions/54c9cbf0-1d8a-4794-9b49-8041447895cc

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_dyadic_slope_to_positive_right_germ_ws01c
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_drift_pos_no_standing_public

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option autoImplicit false

-- The shifted-deficit argument adapts WillR's proof cdf12aa1-07c4-4146-9b56-0e49b7af0cf7.
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P ℱ)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBV : X.BoundedVariation) (τ : Ω → ℝ≥0) (δ : ℕ → ℝ≥0)
    (hδpos : ∀ n, 0 < δ n)
    (hRatio : ∀ n, (δ n : ℝ) ≤ 2 * (δ (n + 1) : ℝ))
    (hCover : ∀ (N : ℕ) (t : ℝ≥0), 0 < t → t < δ N →
      ∃ n : ℕ, N ≤ n ∧ δ (n + 1) ≤ t ∧ t ≤ δ n)
    (hSlope : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * (δ n : ℝ) -
          (X.X (τ ω + δ n) ω - X.X (τ ω) ω)) / (δ n : ℝ))
        atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P,
      ∃ ε : ℝ≥0, 0 < ε ∧ ∀ t : ℝ≥0, 0 < t → t < ε →
        0 < X.X (τ ω + t) ω - X.X (τ ω) ω := by
  have hd := p2m81_bv_root_drift_pos_no_standing_public X q φ hq hφ hroot hBV
  filter_upwards [bv_drift_deficit_ae_monotone_all_times X hBV, hSlope] with ω hMon hSlopeω
  let D (t : ℝ≥0) := X.drift * (t : ℝ) - X.X t ω
  let S (t : ℝ≥0) := D (τ ω + t) - D (τ ω)
  have hSmon : Monotone S := by
    intro t u htu
    change D (τ ω + t) - D (τ ω) ≤ D (τ ω + u) - D (τ ω)
    exact sub_le_sub_right (hMon (add_le_add_right htu (τ ω))) (D (τ ω))
  have hS (t : ℝ≥0) :
      S t = X.drift * (t : ℝ) - (X.X (τ ω + t) ω - X.X (τ ω) ω) := by
    simp only [S, D, NNReal.coe_add]
    ring
  have hSlopeS : Tendsto (fun n : ℕ => S (δ n) / (δ n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hS] using hSlopeω
  obtain ⟨ε, hε, hInc⟩ :=
    bv_dyadic_slope_to_positive_right_germ_ws01c S δ X.drift hd hδpos hSmon hRatio hCover hSlopeS
  refine ⟨ε, hε, fun t ht htε => ?_⟩
  simpa only [hS, sub_sub_cancel] using hInc t ht htε
