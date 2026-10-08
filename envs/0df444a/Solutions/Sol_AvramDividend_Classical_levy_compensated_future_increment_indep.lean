-- Prove2me | solution 1 for AvramDividend.Classical.levy_compensated_future_increment_indep
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:28:45.295005+00:00
-- url     : https://prove2.me/submissions/fc3746c9-a0ff-4833-8ade-2302346237cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) :
    Indep
      (MeasurableSpace.comap
        (fun ω => Real.exp
          (θ * (X.X t ω - X.X s ω) -
            ((t - s : ℝ≥0) : ℝ) * X.ψ θ)) inferInstance)
      (𝓕 s) P := by
  let a : ℝ := ((t - s : ℝ≥0) : ℝ) * X.ψ θ
  let g : Ω → ℝ := fun ω => X.X t ω - X.X s ω
  let f : ℝ → ℝ := fun y => Real.exp (θ * y - a)
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hle :
      (MeasurableSpace.comap f inferInstance).comap g ≤
        (inferInstance : MeasurableSpace ℝ).comap g :=
    MeasurableSpace.comap_mono hf.comap_le
  have hle' :
      MeasurableSpace.comap
        (fun ω => Real.exp (θ * (X.X t ω - X.X s ω) - a))
        inferInstance ≤
      MeasurableSpace.comap
        (fun ω => X.X t ω - X.X s ω) inferInstance := by
    simpa only [MeasurableSpace.comap_comp, Function.comp_def,
      f, g] using hle
  have hi := X.indepIncrements s t hst
  apply indep_of_indep_of_le_left hi
  simpa only [a] using hle'
