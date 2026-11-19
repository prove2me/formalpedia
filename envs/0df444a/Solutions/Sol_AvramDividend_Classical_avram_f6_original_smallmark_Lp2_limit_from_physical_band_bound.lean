-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_smallmark_Lp2_limit_from_physical_band_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T18:45:28.621099+00:00
-- url     : https://prove2.me/submissions/cb2e9595-3cfa-4c21-99a7-cc88a9932945

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_nu_quadratic_tail_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_nu_quadratic_tail_l2_cauchy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : ℕ → ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (C : ℝ)
    (hBandBound : ∀ t n m, n ≤ m →
      dist (M n t) (M m t) ≤
        C * Real.sqrt ((∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
        ENNReal.ofReal (z ^ 2) ∂X.ν).toReal)) :
    ∀ t, ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto (fun n => M n t) atTop (𝓝 L) := by
  have hFinite : ∀ n : ℕ,
      (∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
        ENNReal.ofReal (z ^ 2) ∂X.ν) ≠ ⊤ := by
    intro n
    exact avram_leanlevy_bridge_original_nu_quadratic_tail_finite X n
  intro t
  have hCauchy : CauchySeq (fun n => M n t) :=
    avram_leanlevy_bridge_original_nu_quadratic_tail_l2_cauchy
      X M C hFinite hBandBound t
  exact cauchySeq_tendsto_of_complete hCauchy
