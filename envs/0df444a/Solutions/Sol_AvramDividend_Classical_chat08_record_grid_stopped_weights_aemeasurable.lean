-- Prove2me | solution 1 for AvramDividend.Classical.chat08_record_grid_stopped_weights_aemeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:19:51.176459+00:00
-- url     : https://prove2.me/submissions/9e97bbd5-0bca-4fa8-9ea5-4260a41f911a

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_chat08_killed_first_record_discount_weight_measurable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-! Every uniformly spaced stopped-record weight is a.e.-measurable, for any index shift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (a b q h : ℝ)
    (index : ℕ → ℕ) :
    ∀ n : ℕ, AEMeasurable
      (fun ω : Ω =>
        if twoSidedExitUpTime X (b + (index n : ℝ) * h) ω <
          barrierRuinTime X a ω then
          ENNReal.ofReal (h * Real.exp
            (-(q * (twoSidedExitUpTime X (b + (index n : ℝ) * h) ω).toReal)))
        else 0) P := by
  intro n
  exact (chat08_killed_first_record_discount_weight_measurable X a
    (b + (index n : ℝ) * h) q h).aemeasurable
