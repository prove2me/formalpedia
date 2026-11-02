-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_actual_ruin_stopped_random_grid_four_event_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:23:31.907744+00:00
-- url     : https://prove2.me/submissions/a6675086-5a82-4070-84a2-772e22c5ab91

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_controlled_four_term_discounted_finite_grid_chain
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω)
    (τ : Ω → ℝ≥0)
    (hτruin : (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (hzero : u 0 = 0) (n : ℕ) (hcover : τ ω ≤ u n) :
    let v : ℕ → ℝ≥0 := fun i => min (u i) (τ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let pre : Prop := τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
    let W : ℝ := if pre then Y (τ ω) else riskProcess X x D (τ ω) ω
    E (τ ω) * w W =
      w x + (w (x - rightLimit D 0 ω) - w x) +
      (∑ i ∈ Finset.range n,
        ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))) +
          E (v (i + 1)) *
            (w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
          E (v (i + 1)) *
            (w (Y (v (i + 1))) -
              w (riskProcess X x D (v (i + 1)) ω)))) +
      (if pre then 0 else
        E (τ ω) *
          (w (riskProcess X x D (τ ω) ω) - w (Y (τ ω)))) := by
  classical
  let v : ℕ → ℝ≥0 := fun i => min (u i) (τ ω)
  have hvmono : Monotone v := by
    intro i j hij
    exact min_le_min (hu hij) le_rfl
  have hvzero : v 0 = 0 := by
    simp [v, hzero]
  have hvend : v n = τ ω := by
    exact min_eq_right hcover
  have hgrid :=
    avram_wave5_03_actual_original_controlled_four_term_discounted_finite_grid_chain
      X x q D hD w ω v hvmono hvzero n
  dsimp only at hgrid ⊢
  rw [hvend] at hgrid
  by_cases hpre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
  · simpa only [if_pos hpre, add_zero] using hgrid
  · simp only [if_neg hpre]
    linear_combination hgrid
