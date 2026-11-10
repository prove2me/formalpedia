-- Prove2me | solution 1 for AvramDividend.Classical.avram_gauss_ledger14_original_clipped_strict_prepayment_four_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:06:53.032895+00:00
-- url     : https://prove2.me/submissions/ef86a3c1-03a4-4d06-8c5c-aa720f531ac9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_actual_ruin_stopped_random_grid_four_event_endpoint
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact clipped original-grid identity with the prepayment terminal at every stop. -/
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
    E (τ ω) * w (riskProcess X x D (τ ω) ω) =
      w x + (w (x - rightLimit D 0 ω) - w x) +
      (∑ i ∈ Finset.range n,
        ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))) +
          E (v (i + 1)) *
            (w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
          E (v (i + 1)) *
            (w (Y (v (i + 1))) -
              w (riskProcess X x D (v (i + 1)) ω)))) +
      E (τ ω) * (w (riskProcess X x D (τ ω) ω) - w (Y (τ ω))) := by
  have h :=
    AvramDividend.Classical.avram_wave6_06_actual_ruin_stopped_random_grid_four_event_endpoint
      X x q D hD w ω τ hτruin u hu hzero n hcover
  dsimp only at h ⊢
  by_cases hp : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
  · simp only [if_pos hp] at h
    linear_combination h
  · simpa only [if_neg hp] using h
