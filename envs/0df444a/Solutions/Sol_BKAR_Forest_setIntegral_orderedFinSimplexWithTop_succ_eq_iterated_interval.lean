-- Prove2me | solution 1 for BKAR.Forest.setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:02.4118+00:00
-- url     : https://prove2.me/submissions/df24d00f-7014-46ce-8381-4dc8b59d809c

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_Forest_setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_Icc

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    {top : ℝ} (htop : 0 ≤ top) (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : IntegrableOn f (orderedFinSimplexWithTop top (n + 1))) :
    ∫ ts in orderedFinSimplexWithTop top (n + 1), f ts =
      ∫ t in 0..top,
        ∫ us in orderedFinSimplexWithTop t n, f (Fin.cons t us) := by
  calc
    ∫ ts in orderedFinSimplexWithTop top (n + 1), f ts
        = ∫ t in Set.Icc (0 : ℝ) top,
            ∫ us in orderedFinSimplexWithTop t n, f (Fin.cons t us) := by
          exact setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_Icc
            top n f hf
    _ = ∫ t in 0..top,
          ∫ us in orderedFinSimplexWithTop t n, f (Fin.cons t us) := by
          rw [intervalIntegral.integral_of_le htop]
          rw [setIntegral_congr_set Ioc_ae_eq_Icc]
end BKAR.Forest
