-- Prove2me | solution 1 for BKAR.Forest.orderedContribution_singleton_eq_orderedCubeSectorContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:56.285224+00:00
-- url     : https://prove2.me/submissions/23a18cbe-6c60-4588-b07e-543c5a2a0aa1

import Mathlib.Data.List.NodupEquivFin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Theorems.Thm_BKAR_Forest_edges_eq_singleton_of_singleton_mem_edgeOrders
import Theorems.Thm_BKAR_Forest_orderedCubeSimplex_singleton_eq_funUnique_preimage_Icc
import Theorems.Thm_BKAR_Forest_measurePreserving_funUnique_edgeParam_singleton
import Theorems.Thm_BKAR_Forest_orderedContribution_singleton_eq_setIntegral_Icc_funUnique
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {e : Edge V} (horder : [e] ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedContribution [e] ρ =
      F.orderedCubeSectorContribution [e] ρ := by
  let hedges := F.edges_eq_singleton_of_singleton_mem_edgeOrders horder
  let : Unique F.EdgeParam := F.uniqueEdgeParamOfEdgesSingleton hedges
  let φ : (F.EdgeParam → ℝ) ≃ᵐ ℝ :=
    @MeasurableEquiv.funUnique F.EdgeParam ℝ
      (F.uniqueEdgeParamOfEdgesSingleton hedges) inferInstance
  let H : (F.EdgeParam → ℝ) → ℝ :=
    fun u => mixedPartialList [e].reverse ρ (F.standardInterp u)
  have hsector :
      F.orderedCubeSimplex [e] = φ ⁻¹' Set.Icc (0 : ℝ) 1 := by
    exact F.orderedCubeSimplex_singleton_eq_funUnique_preimage_Icc hedges
  have hmap :
      ∫ u in F.orderedCubeSimplex [e], H u
          ∂(volume : Measure (F.EdgeParam → ℝ)) =
        ∫ t in Set.Icc (0 : ℝ) 1, H (φ.symm t) := by
    rw [hsector]
    have hpre :=
      (F.measurePreserving_funUnique_edgeParam_singleton hedges).setIntegral_preimage_emb
        (MeasurableEquiv.measurableEmbedding φ)
        (fun t : ℝ => H (φ.symm t)) (Set.Icc (0 : ℝ) 1)
    have hcongr :
        ∫ u in φ ⁻¹' Set.Icc (0 : ℝ) 1, H u
            ∂(volume : Measure (F.EdgeParam → ℝ)) =
          ∫ u in φ ⁻¹' Set.Icc (0 : ℝ) 1, H (φ.symm (φ u))
            ∂(volume : Measure (F.EdgeParam → ℝ)) := by
      apply setIntegral_congr_fun
      · exact measurableSet_Icc.preimage φ.measurable
      · intro u _hu
        exact congrArg H (φ.left_inv u).symm
    exact hcongr.trans hpre
  calc
    F.orderedContribution [e] ρ
        = ∫ t in Set.Icc (0 : ℝ) 1, H (φ.symm t) := by
          exact F.orderedContribution_singleton_eq_setIntegral_Icc_funUnique
            hedges ρ
    _ = ∫ u in F.orderedCubeSimplex [e], H u
          ∂(volume : Measure (F.EdgeParam → ℝ)) := hmap.symm
    _ = F.orderedCubeSectorContribution [e] ρ := by
          rw [orderedCubeSectorContribution]
end BKAR.Forest
