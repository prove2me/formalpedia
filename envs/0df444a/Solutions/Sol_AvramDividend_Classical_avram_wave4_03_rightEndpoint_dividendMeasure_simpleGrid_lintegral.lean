-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_rightEndpoint_dividendMeasure_simpleGrid_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:25:07.29499+00:00
-- url     : https://prove2.me/submissions/019829d0-f0e4-4fe8-b18a-8f70dc8485bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ) (c : ℕ → ℝ≥0∞) :
    (∫⁻ t : ℝ, ∑ i ∈ Finset.range n,
      (Ioc (u i : ℝ) (u (i + 1) : ℝ)).indicator
        (fun _ : ℝ => c (i + 1)) t
      ∂dividendMeasure D ω) =
    ∑ i ∈ Finset.range n,
      c (i + 1) *
        ENNReal.ofReal
          (rightLimit D (u (i + 1)) ω -
            rightLimit D (u i) ω) := by
  classical
  calc
    (∫⁻ t : ℝ, ∑ i ∈ Finset.range n,
      (Ioc (u i : ℝ) (u (i + 1) : ℝ)).indicator
        (fun _ : ℝ => c (i + 1)) t
      ∂dividendMeasure D ω) =
      ∑ i ∈ Finset.range n,
        (∫⁻ t : ℝ,
          (Ioc (u i : ℝ) (u (i + 1) : ℝ)).indicator
            (fun _ : ℝ => c (i + 1)) t
          ∂dividendMeasure D ω) := by
        exact lintegral_finset_sum (Finset.range n) (by
          intro i hi
          exact measurable_const.indicator measurableSet_Ioc)
    _ = ∑ i ∈ Finset.range n,
      c (i + 1) *
        (dividendMeasure D ω) (Ioc (u i : ℝ) (u (i + 1) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact lintegral_indicator_const measurableSet_Ioc (c (i + 1))
    _ = ∑ i ∈ Finset.range n,
      c (i + 1) *
        ENNReal.ofReal (rightLimit D (u (i + 1)) ω -
          rightLimit D (u i) ω) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [dividendMeasure_Ioc_rightLimit D hD ω (u i) (u (i + 1))]
