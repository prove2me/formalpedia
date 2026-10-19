-- Prove2me | solution 1 for BookProof.NsScalarFourier.nsScalarFourier_scalarFibreOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:56:58.182374+00:00
-- url     : https://prove2.me/submissions/9f61560d-8e10-441c-b5f4-3de4369d5923

-- Generated from ChapterNsScalarFourier.lean — solution of BookProof.NsScalarFourier.nsScalarFourier_scalarFibreOp
import Mathlib
import Definitions.Def_ChapterNsScalarFourier
import Theorems.Thm_BookProof_NsScalarFourier_nsScalarFourier_apply
import Theorems.Thm_BookProof_NsScalarFourier_scalarFibreOp_apply
import Theorems.Thm_BookProof_NsPartialFourier_nsPartialFourier_fibreOp
import Definitions.Def_ChapterNsScalarVectorCurry
import Definitions.Def_ChapterNsPartialFourier
open BookProof.NsScalarFourier



open MeasureTheory


open BookProof.NsPartialFourier BookProof.NsScalarVectorCurry

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
theorem solution
    (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W))
    (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) :
    nsScalarFourier V W (scalarFibreOp V T g) = scalarFibreOp V T (nsScalarFourier V W g) := by

  rw [nsScalarFourier_apply, scalarFibreOp_apply, scalarFibreOp_apply, nsScalarFourier_apply,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply,
    nsPartialFourier_fibreOp]
