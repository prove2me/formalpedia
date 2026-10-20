-- Prove2me | solution 1 for AvramDividend.Classical.chat03_noexit_integer_horizon_integral_vanish_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T23:28:41.671463+00:00
-- url     : https://prove2.me/submissions/416d3e86-5ad9-4601-bab1-28d60f5cd303

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_both_infinite_passage_event_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_integer_horizon_integral_vanish
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The expected terminal q-scale reward restricted to paths without any
strict upper or lower passage vanishes. No auxiliary measurability
hypotheses remain; those are discharged by first-passage event lemmas.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    Tendsto
      (fun n : ℕ => ∫ ω : Ω,
        if twoSidedExitUpTime X (a - x) ω = ∞ ∧
           twoSidedExitDownTime X (-x) ω = ∞ then
          Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω)
        else 0 ∂P)
      atTop (𝓝 0) := by
  exact chat03_noexit_integer_horizon_integral_vanish
    X q hq W hW a x ha hx0 hxa
    (chat03_both_infinite_passage_event_measurable X (-x) (a - x))
