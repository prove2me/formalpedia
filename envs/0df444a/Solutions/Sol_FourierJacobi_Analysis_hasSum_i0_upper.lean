-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i0_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:41.592343+00:00
-- url     : https://prove2.me/submissions/2f796ebc-08b8-4e02-b106-43e6ca9a67c3

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_i0_upper_reindexed
import Theorems.Thm_FourierJacobi_Analysis_i0_one_sub_ne_zero
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i0_upper_reindexed
import Theorems.Thm_FourierJacobi_Analysis_hasSum_three_geometric


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (neg : Bool) (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I0UpperRow neg => i0Shell t d U V T p.val)
      ((1 - t ^ 2) * i0KInitial neg t d V T * (T * V) * (1 + T * V) * t ^ 2 *
        (1 - i0KRatio neg t d V T)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹) := by
  have hs := (summable_norm_i0_upper_reindexed neg t d U V T ht hK hE).of_norm
  have hrow (e : Fin 2) :
      (∑' n : ℕ × ℕ × ℕ, i0Shell t d U V T (i0UpperRowEquiv neg (e, n)).val) =
      ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * V) ^ (e.val + 1) * t ^ 2) *
        (1 - i0KRatio neg t d V T)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹ := by
    simp_rw [i0_upper_reindexed]
    exact (hasSum_three_geometric _ _ _ _ hK hE ht).tsum_eq
  have he : (∑' n : Fin 2 × ℕ × ℕ × ℕ, i0Shell t d U V T (i0UpperRowEquiv neg n).val) =
      (1 - t ^ 2) * i0KInitial neg t d V T * (T * V) * (1 + T * V) * t ^ 2 *
        (1 - i0KRatio neg t d V T)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ := by
    rw [hs.tsum_prod]
    simp_rw [hrow]
    rw [tsum_fintype, Fin.sum_univ_two]
    norm_num only [Fin.val_zero, Fin.val_one, zero_add, one_add_one_eq_two, pow_one]
    have ht0 := i0_one_sub_ne_zero ht
    have hK0 := i0_one_sub_ne_zero hK
    have hE0 := i0_one_sub_ne_zero hE
    field_simp [ht0, hK0, hE0]
  apply (i0UpperRowEquiv neg).hasSum_iff.mp
  exact he ▸ hs.hasSum
end FourierJacobi.Analysis
