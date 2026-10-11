-- Prove2me | solution 1 for BookProof.NsScalarFourier.scalarFibreOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:03:40.876493+00:00
-- url     : https://prove2.me/submissions/9b608e9d-3da8-48d1-b8a0-e64fb7f7b80e

-- Generated from ChapterNsScalarFourier.lean — solution of BookProof.NsScalarFourier.scalarFibreOp_apply
import Mathlib
import Definitions.Def_ChapterNsScalarFourier
import Definitions.Def_ChapterNsScalarVectorCurry
import Definitions.Def_ChapterNsPartialFourier
open BookProof.NsScalarFourier



open MeasureTheory


open BookProof.NsPartialFourier BookProof.NsScalarVectorCurry
open BookProof.NsPartialFourier

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
variable (V) in

set_option maxHeartbeats 1000000 in
theorem solution (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W))
    (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) :
    scalarFibreOp V T g = curryLI (fibreOp V T (curryLI.symm g)) := rfl
