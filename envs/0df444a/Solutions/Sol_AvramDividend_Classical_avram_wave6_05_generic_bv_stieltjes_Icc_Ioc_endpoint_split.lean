-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_generic_bv_stieltjes_Icc_Ioc_endpoint_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:40:41.016429+00:00
-- url     : https://prove2.me/submissions/a68d9f52-b492-4dbc-84ae-2e393e070785

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

/-- Exact singleton corrections when a closed Stieltjes interval is obtained
from a half-open one. Explicit integrability is essential to the additivity
lemma in the pinned vector-measure API. -/
theorem solution
    (f g : ℝ≥0 → ℝ)
    (hf : BoundedVariationOn f Set.univ)
    (hg : BoundedVariationOn g Set.univ)
    (a b : ℝ≥0) (hab : a ≤ b)
    (hflIoc : hg.vectorMeasure.IntegrableOn (Function.leftLim f) (Ioc a b))
    (hflAt : hg.vectorMeasure.IntegrableOn (Function.leftLim f) ({a} : Set ℝ≥0))
    (hgrIoc : hf.vectorMeasure.IntegrableOn (Function.rightLim g) (Ioc a b))
    (hgrAt : hf.vectorMeasure.IntegrableOn (Function.rightLim g) ({a} : Set ℝ≥0)) :
    ((∫ᵛ t in Icc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
        (∫ᵛ t in Ioc a b, Function.leftLim f t ∂• hg.vectorMeasure) +
          Function.leftLim f a • (Function.rightLim g a - Function.leftLim g a)) ∧
    ((∫ᵛ t in Icc a b, Function.rightLim g t ∂<• hf.vectorMeasure) =
        (∫ᵛ t in Ioc a b, Function.rightLim g t ∂<• hf.vectorMeasure) +
          (Function.rightLim f a - Function.leftLim f a) • Function.rightLim g a) := by
  have hdecomp : ({a} : Set ℝ≥0) ∪ Ioc a b = Icc a b := by
    simpa only [Icc_self] using (Icc_union_Ioc_eq_Icc le_rfl hab)
  have hdisj : Disjoint ({a} : Set ℝ≥0) (Ioc a b) := by
    simp
  have hAt : MeasurableSet ({a} : Set ℝ≥0) := measurableSet_singleton a
  have hIoc : MeasurableSet (Ioc a b) := measurableSet_Ioc
  constructor
  · calc
      (∫ᵛ t in Icc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
          (∫ᵛ t in ({a} : Set ℝ≥0), Function.leftLim f t ∂• hg.vectorMeasure) +
          (∫ᵛ t in Ioc a b, Function.leftLim f t ∂• hg.vectorMeasure) := by
            rw [← hdecomp]
            exact VectorMeasure.setIntegral_union hdisj hAt hIoc hflAt hflIoc
      _ = (∫ᵛ t in Ioc a b, Function.leftLim f t ∂• hg.vectorMeasure) +
          Function.leftLim f a • (Function.rightLim g a - Function.leftLim g a) := by
            simp only [VectorMeasure.integral_singleton, hg.vectorMeasure_singleton,
              ContinuousLinearMap.lsmul_apply]
            abel
  · calc
      (∫ᵛ t in Icc a b, Function.rightLim g t ∂<• hf.vectorMeasure) =
          (∫ᵛ t in ({a} : Set ℝ≥0), Function.rightLim g t ∂<• hf.vectorMeasure) +
          (∫ᵛ t in Ioc a b, Function.rightLim g t ∂<• hf.vectorMeasure) := by
            rw [← hdecomp]
            exact VectorMeasure.setIntegral_union hdisj hAt hIoc hgrAt hgrIoc
      _ = (∫ᵛ t in Ioc a b, Function.rightLim g t ∂<• hf.vectorMeasure) +
          (Function.rightLim f a - Function.leftLim f a) • Function.rightLim g a := by
            simp only [VectorMeasure.integral_singleton, hf.vectorMeasure_singleton,
              ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply]
            abel
