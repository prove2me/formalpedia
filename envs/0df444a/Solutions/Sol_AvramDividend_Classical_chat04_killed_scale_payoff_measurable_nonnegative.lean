-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_scale_payoff_measurable_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:20:09.424214+00:00
-- url     : https://prove2.me/submissions/81db8b2b-3bef-4fed-847d-82970b4bef1a

import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Mathlib.Algebra.Notation.Indicator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

/-- The whole-history killed discounted q-scale payoff is measurable and
    nonnegative at each deterministic observation horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    Measurable
      (({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ∧
    (∀ ω, 0 ≤
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω) := by
  let S : Set Ω := {u | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}
  have hS : MeasurableSet S :=
    chat04_shifted_lower_survival_measurable_no_schedule X x t
  have hRes : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hProd : Measurable (fun u : Ω =>
      Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) := by
    exact measurable_const.mul
      ((chat03_scale_function_borel_measurable X q W hW).comp
        (measurable_const.add hRes))
  constructor
  · exact hProd.indicator hS
  · intro ω
    change 0 ≤ S.indicator
      (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω
    by_cases hs : ω ∈ S
    · have hz : 0 ≤ x + X.X t ω := hs t le_rfl
      rw [Set.indicator_of_mem hs]
      exact mul_nonneg (Real.exp_nonneg _) (hW.2.1 _ hz)
    · rw [Set.indicator_of_notMem hs]
