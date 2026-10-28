-- Prove2me | solution 1 for AvramDividend.Classical.chat04_history_killed_scale_lintegral_lt_top_of_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:51:49.884898+00:00
-- url     : https://prove2.me/submissions/d0770610-b12a-4074-8d53-397ec863f37b

import Theorems.Thm_AvramDividend_Classical_chat04_history_killed_scale_real_ennreal_integral_bridge
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter
open scoped NNReal ENNReal

/-- Fixed-horizon history-killed q-scale expectation is finite under a Laplace gap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (t : ℝ≥0) :
    (∫⁻ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P) < ⊤ := by
  rw [chat04_history_killed_scale_real_ennreal_integral_bridge
    X q hq W hW θ x hθ hψ t]
  exact ENNReal.ofReal_lt_top
