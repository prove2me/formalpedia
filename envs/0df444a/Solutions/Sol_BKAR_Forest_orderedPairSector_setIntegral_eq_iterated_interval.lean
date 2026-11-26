-- Prove2me | solution 1 for BKAR.Forest.orderedPairSector_setIntegral_eq_iterated_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:37:54.948536+00:00
-- url     : https://prove2.me/submissions/3817d4b8-61ed-4a07-902f-d0da4c51e999

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
import Theorems.Thm_BKAR_Forest_orderedPairSector_setIntegral_eq_iterated_Icc

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f orderedPairSector) :
    ∫ z in orderedPairSector, f z =
      ∫ x in 0..(1 : ℝ), ∫ y in 0..x, f (x, y) := by
  calc
    ∫ z in orderedPairSector, f z
        = ∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc (0 : ℝ) x, f (x, y) := by
          exact orderedPairSector_setIntegral_eq_iterated_Icc f hf
    _ = ∫ x in Set.Icc (0 : ℝ) 1, ∫ y in 0..x, f (x, y) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro x hx
          change (∫ y in Set.Icc (0 : ℝ) x, f (x, y)) =
            ∫ y in 0..x, f (x, y)
          rw [intervalIntegral.integral_of_le hx.1]
          rw [setIntegral_congr_set Ioc_ae_eq_Icc]
    _ = ∫ x in 0..(1 : ℝ), ∫ y in 0..x, f (x, y) := by
          rw [intervalIntegral.integral_of_le zero_le_one]
          rw [setIntegral_congr_set Ioc_ae_eq_Icc]
end BKAR.Forest
