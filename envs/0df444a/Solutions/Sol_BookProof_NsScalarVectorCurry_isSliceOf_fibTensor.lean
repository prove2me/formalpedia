-- Prove2me | solution 1 for BookProof.NsScalarVectorCurry.isSliceOf_fibTensor
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:27:06.36086+00:00
-- url     : https://prove2.me/submissions/25ac9764-c3b4-4321-8569-57981d2fc8dd

-- Generated from ChapterNsScalarVectorCurry.lean — solution of BookProof.NsScalarVectorCurry.isSliceOf_fibTensor
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
import Theorems.Thm_BookProof_NsScalarVectorCurry_isSliceOf_fibMk
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.NsScalarVectorCurry



open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}
variable [SigmaFinite μ] [SigmaFinite ν]

set_option maxHeartbeats 1000000 in
theorem solution (t : TensorProduct ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν)) :
    IsSliceOf (fibTensor t) (prodTensor t) := by

  induction t using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero, IsSliceOf]
      have hg := Measure.ae_ae_of_ae_prod (Lp.coeFn_zero ℂ 2 (μ.prod ν))
      filter_upwards [Lp.coeFn_zero (Lp ℂ 2 ν) 2 μ, hg] with x h1 h2
      filter_upwards [h2, Lp.coeFn_zero ℂ 2 ν] with y h3 h4
      rw [h1]
      simpa using h3.symm ▸ h4
  | tmul a c => exact isSliceOf_fibMk a c
  | add t₁ t₂ h₁ h₂ => simpa only [map_add] using h₁.add h₂
