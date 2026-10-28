-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_survival_ennreal_infimum_right_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:57:21.109999+00:00
-- url     : https://prove2.me/submissions/d1e1da64-a217-4e1a-9cdf-9c1bca559d17

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.ContinuousOn
import Theorems.Thm_AvramDividend_Classical_iInf_right_continuous_of_monotone
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_killed_survival_right_continuous_capital
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_monotone_start
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) :
    ContinuousWithinAt
      (fun y : ℝ => ⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P))
      (Ici x) x := by
  let F : ℝ≥0 → ℝ → ℝ≥0∞ :=
    fun t y => ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)
  have hmono : ∀ t, Monotone (F t) := by
    intro t a b hab
    exact ENNReal.ofReal_le_ofReal
      (esscher_weighted_lower_survival_mass_monotone_start
        X θ hθ a b hab t)
  have hright : ∀ t y, ContinuousWithinAt (F t) (Ici y) y := by
    intro t y
    exact ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      (chat04_esscher_killed_survival_right_continuous_capital
        X t θ hθ y)
  change ContinuousWithinAt (fun y => ⨅ t, F t y) (Ici x) x
  exact iInf_right_continuous_of_monotone F hmono hright x
