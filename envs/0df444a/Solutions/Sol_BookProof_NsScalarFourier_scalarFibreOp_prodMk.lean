-- Prove2me | solution 1 for BookProof.NsScalarFourier.scalarFibreOp_prodMk
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:56:57.118978+00:00
-- url     : https://prove2.me/submissions/19455ed8-719b-4342-8640-fecbe00ecd99

-- Generated from ChapterNsScalarFourier.lean — solution of BookProof.NsScalarFourier.scalarFibreOp_prodMk
import Mathlib
import Definitions.Def_ChapterNsScalarFourier
import Theorems.Thm_BookProof_NsScalarFourier_scalarFibreOp_apply
import Theorems.Thm_BookProof_NsScalarFourier_fibreOp_fibMk
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
theorem solution (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W))
    (a : Lp ℂ 2 (volume : Measure V)) (c : Lp ℂ 2 (volume : Measure W)) :
    scalarFibreOp V T (prodMk a c) = prodMk a (T c) := by

  rw [scalarFibreOp_apply, ← curryLI_fibMk (μ := (volume : Measure V)) (ν := (volume : Measure W)),
    LinearIsometryEquiv.symm_apply_apply, fibreOp_fibMk, curryLI_fibMk]
