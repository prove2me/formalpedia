-- Prove2me | solution 1 for BKAR.Forest.orderedContribution_pair_eq_nested_pairMeasurableEquivIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:39:09.536856+00:00
-- url     : https://prove2.me/submissions/5ebfd9e6-979d-4851-8247-1426273a0de2

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
import Theorems.Thm_BKAR_Forest_paramsOfOrder_pair_eq_pairMeasurableEquivOfPair_symm
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_orderedSimplexIntegral_pair


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedContribution [e₁, e₂] ρ =
      ∫ t₁ in 0..(1 : ℝ), ∫ t₂ in 0..t₁,
        mixedPartialList [e₁, e₂].reverse ρ
          (F.standardInterp
            ((F.pairMeasurableEquivOfPair
              (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
              (F.ne_of_pair_mem_edgeOrders horder)).symm (t₁, t₂))) := by
  let hedges := F.edges_eq_pair_of_pair_mem_edgeOrders horder
  let hne := F.ne_of_pair_mem_edgeOrders horder
  let φ : (F.EdgeParam → ℝ) ≃ᵐ (ℝ × ℝ) :=
    F.pairMeasurableEquivOfPair hedges hne
  let H : (F.EdgeParam → ℝ) → ℝ :=
    fun u => mixedPartialList [e₁, e₂].reverse ρ (F.standardInterp u)
  calc
    F.orderedContribution [e₁, e₂] ρ
        = ∫ t₁ in 0..(1 : ℝ), ∫ t₂ in 0..t₁,
            H (F.paramsOfOrder [e₁, e₂] [t₁, t₂]) := by
          rw [orderedContribution, orderedSimplexIntegral_pair]
    _ = ∫ t₁ in 0..(1 : ℝ), ∫ t₂ in 0..t₁,
            H (φ.symm (t₁, t₂)) := by
          apply intervalIntegral.integral_congr
          intro t₁ _ht₁
          apply intervalIntegral.integral_congr
          intro t₂ _ht₂
          change H (F.paramsOfOrder [e₁, e₂] [t₁, t₂]) =
            H (φ.symm (t₁, t₂))
          rw [F.paramsOfOrder_pair_eq_pairMeasurableEquivOfPair_symm hedges hne
            (t₁, t₂)]
    _ = ∫ t₁ in 0..(1 : ℝ), ∫ t₂ in 0..t₁,
        mixedPartialList [e₁, e₂].reverse ρ
          (F.standardInterp (φ.symm (t₁, t₂))) := rfl
end BKAR.Forest
