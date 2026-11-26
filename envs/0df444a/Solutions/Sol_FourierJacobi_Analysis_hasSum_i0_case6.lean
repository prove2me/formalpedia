-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i0_case6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:20:51.077844+00:00
-- url     : https://prove2.me/submissions/d6b7934c-3032-4219-a7ad-d3911d93d902

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Theorems.Thm_FourierJacobi_Analysis_hasSum_three_geometric
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i0_case6_reindexed
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hN : ‖T * V * t / d‖ < 1) :
    HasSum (fun p : I0NegativeRow false => i0Shell t d U V T p.val)
      ((T * V * t / d) / (1 - T * V * t / d)) := by
  have h := hasSum_three_geometric ((1 - t ^ 2) ^ 2 * (T * V * t / d))
    (T * V * t / d) (t ^ 2) (t ^ 2) hN ht ht
  have hn : 1 - t ^ 2 ≠ 0 := sub_ne_zero.mpr (by
    intro he
    rw [← he, norm_one] at ht
    exact (lt_irrefl (1 : ℝ)) ht)
  have he : (1 - t ^ 2) ^ 2 * (T * V * t / d) *
      (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹ =
      (T * V * t / d) / (1 - T * V * t / d) := by
    calc
      _ = ((T * V * t / d) / (1 - T * V * t / d)) *
          ((1 - t ^ 2) * (1 - t ^ 2)⁻¹) *
          ((1 - t ^ 2) * (1 - t ^ 2)⁻¹) := by
        simp only [div_eq_mul_inv]
        ring
      _ = _ := by rw [mul_inv_cancel₀ hn]; simp
  rw [he] at h
  apply (i0NegativeRowEquiv false).hasSum_iff.mp
  convert h using 1
  exact funext fun n => i0_case6_reindexed t d U V T n
end FourierJacobi.Analysis
