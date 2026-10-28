-- Prove2me | solution 1 for AvramDividend.Classical.chat04_standing_history_killed_scale_lintegral_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:59:30.929715+00:00
-- url     : https://prove2.me/submissions/ea94bce4-f622-4d5c-8ad5-ac178ddfce7b

import Theorems.Thm_AvramDividend_Classical_chat04_standing_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every Standing killed q-scale payoff has finite ENNReal expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    (∫⁻ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P) < ⊤ := by
  let S : Set Ω := {u | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}
  let f : Ω → ℝ := fun u =>
    Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)
  have hRaw : Integrable (fun u : Ω => W (x + X.X t u)) P :=
    chat04_standing_scale_fixed_time_integrable
      X hX q hq W hW x t
  have hDisc : Integrable f P := by
    dsimp [f]
    exact hRaw.const_mul _
  have hS : MeasurableSet S := by
    dsimp [S]
    exact chat04_shifted_lower_survival_measurable_no_schedule X x t
  have hKilled : Integrable (S.indicator f) P :=
    hDisc.indicator hS
  change (∫⁻ u, S.indicator (fun v => ENNReal.ofReal (f v)) u ∂P) < ⊤
  calc
    (∫⁻ u, S.indicator (fun v => ENNReal.ofReal (f v)) u ∂P) =
        ∫⁻ u, ENNReal.ofReal (S.indicator f u) ∂P := by
      apply lintegral_congr
      intro u
      by_cases hu : u ∈ S
      · simp only [Set.indicator_of_mem hu]
      · simp only [Set.indicator_of_notMem hu, ENNReal.ofReal_zero]
    _ < ⊤ := hKilled.lintegral_lt_top
