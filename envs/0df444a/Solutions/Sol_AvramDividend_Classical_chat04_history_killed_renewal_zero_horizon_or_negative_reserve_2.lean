-- Prove2me | solution 2 for AvramDividend.Classical.chat04_history_killed_renewal_zero_horizon_or_negative_reserve
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:06:12.782282+00:00
-- url     : https://prove2.me/submissions/fa23f8b9-c458-44c1-a9fb-a1b876d25727

import Theorems.Thm_AvramDividend_Classical_chat04_killed_survival_lintegral_initial_nonnegative
import Theorems.Thm_AvramDividend_Classical_chat04_killed_survival_lintegral_zero_of_negative_initial_reserve

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) (hBoundary : t = 0 ∨ x < 0) :
    (∫⁻ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P) =
    ENNReal.ofReal (W x) := by
  by_cases hx : x < 0
  · exact AvramDividend.Classical.chat04_killed_survival_lintegral_zero_of_negative_initial_reserve
      X q W hW x hx t
  · have ht : t = 0 := hBoundary.resolve_right hx
    subst ht
    exact AvramDividend.Classical.chat04_killed_survival_lintegral_initial_nonnegative X q W x (not_lt.1 hx)
