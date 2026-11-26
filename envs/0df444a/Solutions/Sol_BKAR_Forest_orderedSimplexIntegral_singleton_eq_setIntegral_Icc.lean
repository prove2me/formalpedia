-- Prove2me | solution 1 for BKAR.Forest.orderedSimplexIntegral_singleton_eq_setIntegral_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:55.540921+00:00
-- url     : https://prove2.me/submissions/5a66b5de-deb9-4116-bb87-63217c8a461a

import Mathlib.Data.List.NodupEquivFin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Theorems.Thm_BKAR_orderedSimplexIntegral_singleton


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace BKAR.Forest
theorem _root_.solution
    (e : Edge V) (f : ℝ → ℝ) :
    orderedSimplexIntegral [e] (fun ts => f (ts.getD 0 0)) =
      ∫ t in Set.Icc (0 : ℝ) 1, f t := by
  rw [orderedSimplexIntegral_singleton]
  change (∫ t in 0..(1 : ℝ), f t) =
    ∫ t in Set.Icc (0 : ℝ) 1, f t
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [setIntegral_congr_set Ioc_ae_eq_Icc]
end BKAR.Forest
