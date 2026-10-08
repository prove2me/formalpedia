-- Prove2me | solution 1 for AvramDividend.Classical.levy_small_negative_compensated_div_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T22:33:13.450686+00:00
-- url     : https://prove2.me/submissions/bf3d3e15-a75f-49b1-a5d2-cfff2b2ad4b8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_jump_integrable_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun y : ℝ =>
      (Real.exp (θ * y) - 1 - θ * y) / θ)
      (Ioo (-1 : ℝ) 0) X.ν := by
  have hbase := levy_compensated_jump_integrable_nonneg X θ (le_of_lt hθ)
  have hsubset : Ioo (-1 : ℝ) 0 ⊆ Iio (0 : ℝ) := fun _ hy => hy.2
  have hsmall := hbase.mono_set hsubset
  have hsmall' :
      IntegrableOn (fun y : ℝ =>
        Real.exp (θ * y) - 1 - θ * y) (Ioo (-1 : ℝ) 0) X.ν := by
    refine hsmall.congr_fun ?_ measurableSet_Ioo
    intro y hy
    have hyIn : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy.1, by linarith [hy.2]⟩
    simp only [Set.indicator_of_mem hyIn, mul_one]
  have hnorm : IntegrableOn (fun y : ℝ =>
      θ⁻¹ * (Real.exp (θ * y) - 1 - θ * y))
      (Ioo (-1 : ℝ) 0) X.ν := hsmall'.const_mul _
  simpa only [div_eq_mul_inv, mul_comm] using hnorm
