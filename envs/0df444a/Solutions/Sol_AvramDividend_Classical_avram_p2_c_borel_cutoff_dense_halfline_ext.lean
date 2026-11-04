-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_cutoff_dense_halfline_ext
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:01:33.789201+00:00
-- url     : https://prove2.me/submissions/d5834043-65dd-48d6-bcda-e1ef97d9c803

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_finite_measure_ext_of_dense_halfline_tests

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Dense halfline tests identify finite-cutoff restrictions even for infinite ambient measures. -/
theorem solution
    (μ ν : Measure ℝ) (c : ℝ)
    (hμfin : μ (Iic c) ≠ ⊤) (hνfin : ν (Iic c) ≠ ⊤)
    (D : Set ℝ) (hDense : Dense D)
    (hTests : ∀ a : ℝ, a ∈ D → μ (Iic a ∩ Iic c) = ν (Iic a ∩ Iic c)) :
    μ.restrict (Iic c) = ν.restrict (Iic c) := by
  haveI : IsFiniteMeasure (μ.restrict (Iic c)) :=
    (isFiniteMeasure_restrict).2 hμfin
  haveI : IsFiniteMeasure (ν.restrict (Iic c)) :=
    (isFiniteMeasure_restrict).2 hνfin
  apply AvramDividend.Classical.avram_p2_c_borel_finite_measure_ext_of_dense_halfline_tests
      (μ.restrict (Iic c)) (ν.restrict (Iic c)) D hDense
  intro a ha
  simpa only [Measure.restrict_apply measurableSet_Iic] using hTests a ha
