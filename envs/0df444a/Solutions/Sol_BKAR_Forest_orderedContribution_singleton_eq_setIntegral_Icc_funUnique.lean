-- Prove2me | solution 1 for BKAR.Forest.orderedContribution_singleton_eq_setIntegral_Icc_funUnique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:36:17.714854+00:00
-- url     : https://prove2.me/submissions/02051aa8-d756-423d-a594-a1c6bfa894db

import Mathlib.Data.List.NodupEquivFin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Theorems.Thm_BKAR_Forest_paramsOfOrder_singleton_eq_funUnique_symm
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_orderedSimplexIntegral_singleton


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {e : Edge V} (hedges : F.edges = {e})
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedContribution [e] ρ =
      ∫ t in Set.Icc (0 : ℝ) 1,
        mixedPartialList [e].reverse ρ
          (F.standardInterp
            ((@MeasurableEquiv.funUnique F.EdgeParam ℝ
              (F.uniqueEdgeParamOfEdgesSingleton hedges) inferInstance).symm t)) := by
  let : Unique F.EdgeParam := F.uniqueEdgeParamOfEdgesSingleton hedges
  let φ : (F.EdgeParam → ℝ) ≃ᵐ ℝ :=
    @MeasurableEquiv.funUnique F.EdgeParam ℝ
      (F.uniqueEdgeParamOfEdgesSingleton hedges) inferInstance
  let H : (F.EdgeParam → ℝ) → ℝ :=
    fun u => mixedPartialList [e].reverse ρ (F.standardInterp u)
  have hparams :
      ∀ t : ℝ, H (F.paramsOfOrder [e] [t]) = H (φ.symm t) := by
    intro t
    rw [F.paramsOfOrder_singleton_eq_funUnique_symm hedges t]
  calc
    F.orderedContribution [e] ρ
        = ∫ t in 0..(1 : ℝ), H (F.paramsOfOrder [e] [t]) := by
          rw [orderedContribution, orderedSimplexIntegral_singleton]
    _ = ∫ t in 0..(1 : ℝ), H (φ.symm t) := by
          apply intervalIntegral.integral_congr
          intro t _ht
          exact hparams t
    _ = ∫ t in Set.Icc (0 : ℝ) 1, H (φ.symm t) := by
          rw [intervalIntegral.integral_of_le zero_le_one]
          rw [setIntegral_congr_set Ioc_ae_eq_Icc]
    _ = ∫ t in Set.Icc (0 : ℝ) 1,
          mixedPartialList [e].reverse ρ (F.standardInterp (φ.symm t)) := rfl
end BKAR.Forest
