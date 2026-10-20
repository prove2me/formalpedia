-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_eq_stieltjes_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:00:57.756534+00:00
-- url     : https://prove2.me/submissions/9724e635-4ca0-4204-a6ce-eb0f2cbb37db

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_eq_stieltjes
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ) :
    ∃ h : ∀ ω : Ω,
      Monotone (fun t : ℝ => runningSup X t.toNNReal ω),
      barrierSupValue X a q =
        ∫⁻ ω, ∫⁻ t in paymentTimes (barrierRuinTime X a ω),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂
          ((h ω).stieltjesFunction.measure) ∂P := by
  classical
  let h : ∀ ω : Ω, Monotone (fun t : ℝ => runningSup X t.toNNReal ω) :=
    fun ω => Classical.choose (runningSup_dividendMeasure_eq_stieltjes X ω)
  have hEq (ω : Ω) :
      dividendMeasure (runningSup X) ω =
        (h ω).stieltjesFunction.measure :=
    Classical.choose_spec (runningSup_dividendMeasure_eq_stieltjes X ω)
  refine ⟨h, ?_⟩
  unfold barrierSupValue
  apply lintegral_congr
  intro ω
  rw [hEq ω]
