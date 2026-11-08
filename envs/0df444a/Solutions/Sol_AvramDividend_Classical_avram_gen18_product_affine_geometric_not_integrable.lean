-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen18_product_affine_geometric_not_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:15:19.544945+00:00
-- url     : https://prove2.me/submissions/cc63fcbe-4df1-47f6-b665-06e5b75b0703

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gen17_actual_affine_hjb_geometric_not_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section

/-- A nonintegrable HJB profile remains nonintegrable under independent randomness. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : unitInterval) (hp : p ≠ 0) (hhalf : (p : ℝ) = 1 / 2) :
    ¬ Integrable (fun z : Ω × ℕ =>
      (3 : ℝ) + 1 / (16 * ((2 : ℝ) ^ z.2) ^ 2) -
        4 * Real.sqrt (1 / (16 * ((2 : ℝ) ^ z.2) ^ 2)) -
        2 / Real.sqrt (1 / (16 * ((2 : ℝ) ^ z.2) ^ 2)))
      (μ.prod (geometricMeasure p)) := by
  have hμ : μ ≠ 0 := by
    intro heq
    have hmass : μ Set.univ = 1 := measure_univ
    rw [heq] at hmass
    simpa using hmass
  intro hprod
  have hbase : Integrable (fun k : ℕ =>
      (3 : ℝ) + 1 / (16 * ((2 : ℝ) ^ k) ^ 2) -
        4 * Real.sqrt (1 / (16 * ((2 : ℝ) ^ k) ^ 2)) -
        2 / Real.sqrt (1 / (16 * ((2 : ℝ) ^ k) ^ 2)))
      (geometricMeasure p) := by
    exact (Integrable.comp_snd_iff (μ := μ) (ν := geometricMeasure p) hμ).mp hprod
  exact (AvramDividend.Classical.avram_gen17_actual_affine_hjb_geometric_not_integrable
    p hp hhalf) hbase
