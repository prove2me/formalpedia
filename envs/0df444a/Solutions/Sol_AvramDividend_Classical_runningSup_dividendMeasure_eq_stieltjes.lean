-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_eq_stieltjes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T11:31:25.955873+00:00
-- url     : https://prove2.me/submissions/1822d923-3c1d-4fe0-a47f-dfa07174ece7

import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ∃ h : Monotone (fun t : ℝ => runningSup X t.toNNReal ω),
      dividendMeasure (runningSup X) ω = h.stieltjesFunction.measure := by
  have hMono :
      Monotone (fun t : ℝ => runningSup X t.toNNReal ω) := by
    exact (runningSup_monotone_and_path_le X ω).1.comp
      (fun _ _ hst => Real.toNNReal_mono hst)
  refine ⟨hMono, ?_⟩
  simp only [dividendMeasure, dif_pos hMono]
