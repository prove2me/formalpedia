-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_stationary_dyadic_ae_positive_cauchy_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:29:26.767506+00:00
-- url     : https://prove2.me/submissions/515cb933-518f-4cc3-87c4-862f495bfe39

import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_bv_actual_deficit_ae_positive_time_cauchy_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_positive_real_actual_quotient_formula_ws01c
open MeasureTheory Filter Topology
open scoped NNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        CauchySeq (fun n : ℕ =>
          X.drift -
            (X.X (Real.toNNReal t + ((1 : ℝ≥0) / 2) ^ n) ω -
              X.X (Real.toNNReal t) ω) /
                (((1 : ℝ≥0) / 2) ^ n : ℝ)) := by
  filter_upwards [bv_actual_deficit_ae_positive_time_cauchy_ws01c X hBV] with ω hω
  filter_upwards [hω, ae_restrict_mem measurableSet_Ioc] with t ht htI
  have h := fun n => bv_positive_real_actual_quotient_formula_ws01c X.drift (fun u => X.X u ω) t htI.1.le n
  simpa only [h] using ht
