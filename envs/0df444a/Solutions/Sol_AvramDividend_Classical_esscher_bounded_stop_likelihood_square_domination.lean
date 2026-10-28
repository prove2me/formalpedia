-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_likelihood_square_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:02:36.965698+00:00
-- url     : https://prove2.me/submissions/28beb2ea-32e3-45e6-bf39-b4869aa8c180

import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stopped_density_probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0) (H : ℝ≥0)
    (hbound : ∀ ω, τ ω ≤ H) (ω : Ω) :
    Real.exp ((2 * θ) * X.X (τ ω) ω -
        2 * (τ ω : ℝ) * X.ψ θ) ≤
      Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|) *
        Real.exp ((2 * θ) * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ (2 * θ)) := by
  let c : ℝ := X.ψ (2 * θ) - 2 * X.ψ θ
  have ht0 : (0 : ℝ) ≤ (τ ω : ℝ) := NNReal.coe_nonneg (τ ω)
  have htH : (τ ω : ℝ) ≤ (H : ℝ) :=
    NNReal.coe_le_coe.mpr (hbound ω)
  have hc : (τ ω : ℝ) * c ≤ (H : ℝ) * |c| := by
    calc
      (τ ω : ℝ) * c ≤ (τ ω : ℝ) * |c| :=
        mul_le_mul_of_nonneg_left (le_abs_self c) ht0
      _ ≤ (H : ℝ) * |c| :=
        mul_le_mul_of_nonneg_right htH (abs_nonneg c)
  calc
    Real.exp ((2 * θ) * X.X (τ ω) ω -
        2 * (τ ω : ℝ) * X.ψ θ) =
      Real.exp ((2 * θ) * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ (2 * θ)) *
      Real.exp ((τ ω : ℝ) * c) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [c]
        ring
    _ ≤ Real.exp ((2 * θ) * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ (2 * θ)) *
      Real.exp ((H : ℝ) * |c|) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hc)
          (Real.exp_pos _).le
    _ = Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|) *
        Real.exp ((2 * θ) * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ (2 * θ)) := by
        dsimp [c]
        ac_rfl
