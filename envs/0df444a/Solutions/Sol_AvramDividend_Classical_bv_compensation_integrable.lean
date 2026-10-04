-- Prove2me | solution 1 for AvramDividend.Classical.bv_compensation_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T09:53:14.248301+00:00
-- url     : https://prove2.me/submissions/c50b8ff2-31af-4c0a-b7c7-88bae525e866

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation) (θ : ℝ) :
    IntegrableOn
      (fun y : ℝ => θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
      (Iio (0 : ℝ)) X.ν := by
  have hsmall :
      IntegrableOn (fun y : ℝ => y) (Ioo (-1 : ℝ) 0) X.ν := by
    refine ⟨by fun_prop, ?_⟩
    change (∫⁻ y in Ioo (-1 : ℝ) 0, ‖(y : ℝ)‖ₑ ∂X.ν) < ⊤
    simpa only [Real.enorm_eq_ofReal_abs] using hbv.2
  have hmul :
      IntegrableOn (fun y : ℝ => θ * y) (Ioo (-1 : ℝ) 0) X.ν :=
    hsmall.const_mul θ
  have hs :
      Ioo (-1 : ℝ) 1 ∩ Iio 0 = Ioo (-1 : ℝ) 0 := by
    ext y
    constructor
    · intro h
      exact ⟨h.1.1, h.2⟩
    · intro h
      exact ⟨⟨h.1, lt_trans h.2 (by norm_num)⟩, h.2⟩
  have hint :
      IntegrableOn
        ((Ioo (-1 : ℝ) 1).indicator (fun y : ℝ => θ * y))
        (Iio (0 : ℝ)) X.ν := by
    apply (integrableOn_indicator_iff measurableSet_Ioo).2
    simpa only [hs] using hmul
  have heq :
      (fun y : ℝ => θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) =
        (Ioo (-1 : ℝ) 1).indicator (fun y : ℝ => θ * y) := by
    funext y
    by_cases hy : y ∈ Ioo (-1 : ℝ) 1
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  simpa only [heq] using hint
