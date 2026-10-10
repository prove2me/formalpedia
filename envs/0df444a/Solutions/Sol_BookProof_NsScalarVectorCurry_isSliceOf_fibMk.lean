-- Prove2me | solution 1 for BookProof.NsScalarVectorCurry.isSliceOf_fibMk
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:22.015289+00:00
-- url     : https://prove2.me/submissions/d96e2e7e-f9d2-4691-97d5-43986aa86e35

-- Generated from ChapterNsScalarVectorCurry.lean — solution of BookProof.NsScalarVectorCurry.isSliceOf_fibMk
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
open BookProof.NsScalarVectorCurry



open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}
variable [SigmaFinite μ] [SigmaFinite ν]

set_option maxHeartbeats 1000000 in
theorem solution (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) : IsSliceOf (fibMk a c) (prodMk a c) := by

  have hprod := Measure.ae_ae_of_ae_prod (coeFn_prodMk a c)
  filter_upwards [coeFn_fibMk a c, hprod] with x h1 h2
  filter_upwards [h2, Lp.coeFn_smul ((a : V → ℂ) x) c] with y h3 h4
  rw [h1, h4, h3]
  simp [smul_eq_mul]
