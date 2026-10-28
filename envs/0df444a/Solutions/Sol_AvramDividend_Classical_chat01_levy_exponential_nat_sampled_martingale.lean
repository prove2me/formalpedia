-- Prove2me | solution 1 for AvramDividend.Classical.chat01_levy_exponential_nat_sampled_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:10:59.48032+00:00
-- url     : https://prove2.me/submissions/de45b65f-e848-42d8-84e9-63750aca83f6

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_nat_sampling_martingale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal

/-- Discrete sampling of the canonical compensated Lévy exponential
    martingale along any monotone time schedule. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (e : ℕ → ℝ≥0) (he : Monotone e) :
    Martingale
      (fun (n : ℕ) (ω : Ω) =>
        Real.exp (θ * X.X (e n) ω -
          (e n : ℝ) * laplaceExponent X.c X.σ X.ν θ))
      ({ seq := fun (n : ℕ) => 𝓕 (e n)
         mono' := by
           intro i j hij
           exact 𝓕.mono (he hij)
         le' := by
           intro n
           exact 𝓕.le (e n) } : Filtration ℕ mΩ) P := by
  exact chat01_monotone_nat_sampling_martingale
    e he (levy_compensated_exponential_martingale X θ hθ)
