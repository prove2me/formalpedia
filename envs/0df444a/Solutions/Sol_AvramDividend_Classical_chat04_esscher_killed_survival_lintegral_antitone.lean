-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_killed_survival_lintegral_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:17:38.413994+00:00
-- url     : https://prove2.me/submissions/9e3b2f92-c227-4884-bd28-5d4871b816e6

import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_killed_survival_real_to_lintegral
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_antitone
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ)
    (t u : ℝ≥0) (htu : t ≤ u) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (θ * X.X u ω -
            (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P) ≤
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (θ * X.X t ω -
            (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P) := by
  rw [chat04_esscher_killed_survival_real_to_lintegral X x u θ hθ,
      chat04_esscher_killed_survival_real_to_lintegral X x t θ hθ]
  exact ENNReal.ofReal_le_ofReal
    (esscher_weighted_lower_survival_mass_antitone X θ hθ x t u htu)
