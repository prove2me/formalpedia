-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB50_original_postpaid_upper_strip_occupation_integral_le_prepaid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:17:01.543058+00:00
-- url     : https://prove2.me/submissions/0009638f-cde9-44b7-9da1-df72673166c0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_postpaid_upper_strip_indicator_le_true_prepaid
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω)
    (hIpost : IntegrableOn
      (fun t : ℝ =>
        if t < (ρ ω : ℝ) ∧
            b < x + X.X (Real.toNNReal t) ω -
              rightLimit D (Real.toNNReal t) ω
        then (1 : ℝ) else 0)
      (Ioo (0 : ℝ) (n : ℝ)) volume)
    (hIpre : IntegrableOn
      (fun t : ℝ =>
        if t < (ρ ω : ℝ) ∧
            b < riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0)
      (Ioo (0 : ℝ) (n : ℝ)) volume) :
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
          b < x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) ≤
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
          b < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) := by
  apply integral_mono_ae hIpost hIpre
  apply Filter.Eventually.of_forall
  intro t
  by_cases ht : t < (ρ ω : ℝ)
  · have hpoint :=
      avram_gbB49_original_postpaid_upper_strip_indicator_le_true_prepaid
        X x b D hD ω (Real.toNNReal t)
    simpa only [ht, true_and, if_true] using hpoint
  · simp [ht]
