-- Prove2me | solution 1 for Ehrhart.TranslatedGaussianLatticeAsymptotics.tendsto_roundedLatticeExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/ae6575bc-0d6b-4fac-8412-d9988be55405

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TranslatedGaussianLatticeAsymptotics_roundedLatticeExponent_norm_sub_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TranslatedGaussianLatticeAsymptotics
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators
namespace Ehrhart.TranslatedGaussianLatticeAsymptotics
theorem _root_.solution {n : ℕ}
    (u : Space n) :
    Tendsto (fun k : ℕ => roundedLatticeExponent k u)
      atTop (𝓝 u) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun k => norm_nonneg _)
    ?_ (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  exact roundedLatticeExponent_norm_sub_le
    (lt_of_lt_of_le Nat.zero_lt_one hk) u
end Ehrhart.TranslatedGaussianLatticeAsymptotics
