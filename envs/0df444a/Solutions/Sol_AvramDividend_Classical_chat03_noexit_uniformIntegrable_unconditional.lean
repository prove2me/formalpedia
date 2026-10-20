-- Prove2me | solution 1 for AvramDividend.Classical.chat03_noexit_uniformIntegrable_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T23:28:23.277747+00:00
-- url     : https://prove2.me/submissions/e6fb0e2e-2752-4fe5-ad0c-d1396ca615a3

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_both_infinite_passage_event_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_uniformIntegrable_of_measurable_event
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Uniform integrability of the entire finite-time no-passage payoff
family follows with all event and observable measurability discharged.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    UniformIntegrable
      (fun t : ℝ≥0 => fun ω : Ω =>
        if twoSidedExitUpTime X (a - x) ω = ∞ ∧
           twoSidedExitDownTime X (-x) ω = ∞ then
          Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)
        else 0)
      (1 : ℝ≥0∞) P := by
  exact chat03_noexit_uniformIntegrable_of_measurable_event
    X q hq W hW a x ha hx0 hxa
    (chat03_both_infinite_passage_event_measurable X (-x) (a - x))
