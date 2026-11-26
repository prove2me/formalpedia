-- Prove2me | solution 1 for FixedOrderFactor.tendsto_zetaN_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:07.668237+00:00
-- url     : https://prove2.me/submissions/011310a0-34c7-41d0-bb7c-5f059730bc0e

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order
public import Theorems.Thm_FixedOrderFactor_zetaN_empty_le
public import Theorems.Thm_FixedOrderFactor_one_le_zetaN


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution : Tendsto (fun s => zetaN ∅ s) atTop (𝓝 1) := by
  have hc : Tendsto (fun s : ℕ => 1 + (1 / 2 : ℝ) ^ (s - 2) * zetaN ∅ 2) atTop (𝓝 1) := by
    have h0 : Tendsto (fun s : ℕ => (1 / 2 : ℝ) ^ (s - 2)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_sub_atTop_nat 2)
    simpa using tendsto_const_nhds.add (h0.mul_const (zetaN ∅ 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with s hs using one_le_zetaN ∅ hs
  · filter_upwards [eventually_ge_atTop 2] with s hs using zetaN_empty_le s hs
end FixedOrderFactor
