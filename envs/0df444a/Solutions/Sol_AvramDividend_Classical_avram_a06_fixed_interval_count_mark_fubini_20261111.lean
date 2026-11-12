-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_fixed_interval_count_mark_fubini_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:04:36.76584+00:00
-- url     : https://prove2.me/submissions/e2c1c4c7-d0b1-49c8-9942-1f0dafa0f8ea

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_count_independent_of_fixed_mark_interval_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_independent_stream_integral_disintegration_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Ω → Fin (n + 1) → ℕ) (Y : Ω → ℕ → ℝ)
    (hN : Measurable N) (hY : Measurable Y)
    (hSeparate : IndepFun N Y P) (a b : ℕ)
    (F : ((Fin (n + 1) → ℕ) × ℝ) → ℂ)
    (hF : Integrable F ((Measure.map N P).prod
      (Measure.map (fun ω => ∑ j ∈ Finset.Ico a b, Y ω j) P))) :
    (∫ ω, F (N ω, ∑ j ∈ Finset.Ico a b, Y ω j) ∂P) =
      ∫ m, ∫ z, F (m, z) ∂(Measure.map
        (fun ω => ∑ j ∈ Finset.Ico a b, Y ω j) P) ∂(Measure.map N P) := by
  let Z : Ω → ℝ := fun ω => ∑ j ∈ Finset.Ico a b, Y ω j
  have hZ : Measurable Z :=
    Finset.measurable_sum (Finset.Ico a b)
      (fun j _ => (measurable_pi_apply j).comp hY)
  have hInd : IndepFun N Z P :=
    AvramDividend.Classical.avram_a06_count_independent_of_fixed_mark_interval_20261111
      P n N Y hSeparate a b
  exact
    AvramDividend.Classical.avram_a06_independent_stream_integral_disintegration_20261111
      P N Z hN hZ hInd F hF
