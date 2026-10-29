-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_raw_clock_positive_germ_of_cap_slopes_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:12:05.854021+00:00
-- url     : https://prove2.me/submissions/c9a69b94-52e8-4747-acee-ffec857e6478

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_post_clock_positive_germ_of_dyadic_zero_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_countable_cap_germs_to_finite_raw_clock_ws01c

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
    (τ : Ω → ℝ≥0∞) (δ : ℕ → ℝ≥0)
    (hδpos : ∀ n, 0 < δ n)
    (hRatio : ∀ n, (δ n : ℝ) ≤ 2 * (δ (n + 1) : ℝ))
    (hCover : ∀ (N : ℕ) (t : ℝ≥0), 0 < t → t < δ N →
      ∃ n : ℕ, N ≤ n ∧ δ (n + 1) ≤ t ∧ t ≤ δ n)
    (hCapSlope : ∀ N : ℕ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * (δ n : ℝ) -
          (X.X ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal + δ n) ω -
            X.X ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal) ω)) /
          (δ n : ℝ))
        atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P,
      τ ω < ⊤ →
      ∃ ε : ℝ≥0, 0 < ε ∧
        ∀ t : ℝ≥0, 0 < t → t < ε →
          0 < X.X ((τ ω).toNNReal + t) ω -
            X.X ((τ ω).toNNReal) ω := by
  let G : ℝ≥0 → Ω → Prop := fun s ω =>
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ t : ℝ≥0, 0 < t → t < ε →
        0 < X.X (s + t) ω - X.X s ω
  have hCapGerms : ∀ N : ℕ, ∀ᵐ ω ∂P,
      G ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal) ω := by
    intro N
    exact bv_post_clock_positive_germ_of_dyadic_zero_ws01c
      X hStanding hBV
      (fun ω => (τ ω ⊓ (N : ℝ≥0∞)).toNNReal) δ
      hδpos hRatio hCover (hCapSlope N)
  exact bv_countable_cap_germs_to_finite_raw_clock_ws01c
    P τ G hCapGerms
