-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i0_case1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:20:31.295863+00:00
-- url     : https://prove2.me/submissions/282b5d9f-0f09-425f-8317-dfe9aa81cead

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Theorems.Thm_FourierJacobi_Analysis_i0_case1_reindexed
import Theorems.Thm_FourierJacobi_Analysis_hasSum_three_geometric

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1) :
    HasSum (fun p : I0PositiveRow false => i0Shell t d U V T p.val)
      (1 - d * T * V * t)⁻¹ := by
  have h := hasSum_three_geometric ((1 - t ^ 2) ^ 2)
    (d * T * V * t) (t ^ 2) (t ^ 2) hP ht ht
  have hn : 1 - t ^ 2 ≠ 0 := sub_ne_zero.mpr (by
    intro he
    rw [← he, norm_one] at ht
    exact (lt_irrefl (1 : ℝ)) ht)
  have he : (1 - t ^ 2) ^ 2 * (1 - d * T * V * t)⁻¹ *
      (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹ = (1 - d * T * V * t)⁻¹ := by
    calc
      _ = (1 - d * T * V * t)⁻¹ *
          ((1 - t ^ 2) * (1 - t ^ 2)⁻¹) *
          ((1 - t ^ 2) * (1 - t ^ 2)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hn]; simp
  rw [he] at h
  apply (i0PositiveRowEquiv false).hasSum_iff.mp
  convert h using 1
  exact funext fun n => i0_case1_reindexed t d U V T n
end FourierJacobi.Analysis
