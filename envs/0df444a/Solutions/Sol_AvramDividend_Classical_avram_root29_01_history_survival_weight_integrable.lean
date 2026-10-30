-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_history_survival_weight_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:41:21.972989+00:00
-- url     : https://prove2.me/submissions/e580e2d6-5679-48a4-8d52-50d0fc348929

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_monotone_start
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

/-- Under the true source Lévy measure, the history-weighted future survival
mass is integrable, dominated by the normalised Esscher exponential. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) (s u : ℝ≥0) :
    Integrable
      (fun ω : Ω =>
        ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
          (fun ω => Real.exp
            (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
              (∫ ζ,
                ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ (x + X.X s ω) + X.X v ζ}).indicator
                  (fun ζ => Real.exp
                    (θ * X.X u ζ - (u : ℝ) *
                      laplaceExponent X.c X.σ X.ν θ)) ζ ∂P)) ω) P := by
  let B : Set Ω :=
    {ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}
  let M : Ω → ℝ := fun ω =>
    Real.exp (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)
  let F : ℝ → ℝ := fun z =>
    ∫ ζ, ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ z + X.X v ζ}).indicator
      (fun ζ => Real.exp
        (θ * X.X u ζ - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ζ ∂P
  have hB : MeasurableSet B :=
    chat04_shifted_lower_survival_measurable_no_schedule X x s
  have hXs : Measurable (X.X s) := (X.adapted s).mono (𝓕.le s) le_rfl
  have hMm : Measurable M :=
    Real.continuous_exp.measurable.comp
      ((measurable_const.mul hXs).sub measurable_const)
  have hFmono : Monotone F := by
    intro a b hab
    exact esscher_weighted_lower_survival_mass_monotone_start
      X θ hθ a b hab u
  have hFm : Measurable F := hFmono.measurable
  have hG : Measurable (fun ω => M ω * F (x + X.X s ω)) :=
    hMm.mul (hFm.comp (measurable_const.add hXs))
  have hUnit (z : ℝ) : 0 ≤ F z ∧ F z ≤ 1 :=
    esscher_weighted_lower_survival_mass_unit_interval X θ hθ z u
  have hIntM : Integrable M P := esscher_exp_process_integrable X θ hθ s
  change Integrable (B.indicator (fun ω => M ω * F (x + X.X s ω))) P
  apply hIntM.mono' (hG.indicator hB).aestronglyMeasurable
  filter_upwards with ω
  by_cases hw : ω ∈ B
  · rw [Set.indicator_of_mem hw]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (hUnit _).1)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (hUnit _).2
  · rw [Set.indicator_of_notMem hw, norm_zero]
    exact (Real.exp_pos _).le
