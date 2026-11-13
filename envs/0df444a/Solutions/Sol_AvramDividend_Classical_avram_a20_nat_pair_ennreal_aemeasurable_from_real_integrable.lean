-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_nat_pair_ennreal_aemeasurable_from_real_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:05:16.96302+00:00
-- url     : https://prove2.me/submissions/8bffdac0-d15c-4bd5-919d-cf1bed9a62e5

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

/-- Real integrability of the doubled count implies ENNReal a.e. measurability. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ)
    (hI : Integrable (fun ω => 2 * (K ω : ℝ)) P) :
    AEMeasurable (fun ω => (K ω : ℝ≥0∞)) P := by
  have hDouble : AEMeasurable (fun ω => 2 * (K ω : ℝ)) P :=
    hI.aestronglyMeasurable.aemeasurable
  have hDivide : AEMeasurable
      (fun ω => (2 * (K ω : ℝ)) / (2 : ℝ)) P :=
    hDouble.div_const 2
  have hReal : AEMeasurable (fun ω => (K ω : ℝ)) P := by
    convert hDivide using 1
    funext ω
    ring
  simpa only [Function.comp_def, ENNReal.ofReal_natCast] using
    (ENNReal.measurable_ofReal.comp_aemeasurable hReal)
