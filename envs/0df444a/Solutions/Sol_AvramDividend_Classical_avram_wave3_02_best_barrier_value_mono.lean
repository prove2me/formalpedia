-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_best_barrier_value_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T18:07:39.176323+00:00
-- url     : https://prove2.me/submissions/51c1e504-9a80-4087-b4e4-907eb318f9d8

import Mathlib.Order.CompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_value_monotone_in_initial_capital
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The best actual expected dividend value among all nonnegative constant
barriers is monotone in the nonnegative starting capital. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    MonotoneOn (fun x : ℝ =>
      ⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) (Ici 0) := by
  intro x hx y hy hxy
  refine iSup_le fun a => ?_
  refine iSup_le fun ha => ?_
  have hm := avram_wave3_02_value_monotone_in_initial_capital
    X hX q hq W hW a ha hx hy hxy
  exact le_iSup_of_le a (le_iSup_of_le ha hm)
