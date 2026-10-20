-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_Ioc_rightLim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:10:35.392482+00:00
-- url     : https://prove2.me/submissions/9cfeac9e-554c-4943-b5e1-d8068d46f699

import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_eq_stieltjes

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s t : ℝ) :
    (dividendMeasure (runningSup X) ω) (Set.Ioc s t) =
      ENNReal.ofReal
        (Function.rightLim (fun r : ℝ => runningSup X r.toNNReal ω) t -
         Function.rightLim (fun r : ℝ => runningSup X r.toNNReal ω) s) := by
  obtain ⟨hMono, hMeasure⟩ :=
    runningSup_dividendMeasure_eq_stieltjes X ω
  rw [hMeasure]
  rw [StieltjesFunction.measure_Ioc]
  simp only [Monotone.stieltjesFunction_eq]
