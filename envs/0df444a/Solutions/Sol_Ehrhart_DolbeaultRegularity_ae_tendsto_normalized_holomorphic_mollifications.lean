-- Prove2me | solution 1 for Ehrhart.DolbeaultRegularity.ae_tendsto_normalized_holomorphic_mollifications
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/9250910b-dae7-4da8-9fd0-be26f4c21080

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultRegularity_complexShrinkingBump_rOut_tendsto
import Theorems.Thm_Ehrhart_DolbeaultRegularity_complexShrinkingBump_radius_ratio

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.DolbeaultRegularity
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
namespace Ehrhart.DolbeaultRegularity
theorem _root_.solution {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n))) :
    ∀ᵐ z : TorusCharacters.LogSpace n
      ∂(volume : Measure (TorusCharacters.LogSpace n)),
      Tendsto (fun k : ℕ =>
        ((complexShrinkingBump (n := n) k).normed
          (volume : Measure (TorusCharacters.LogSpace n))
         ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
           (volume : Measure (TorusCharacters.LogSpace n))]
             g) z)
        atTop (nhds (g z)) := by
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (complexShrinkingBump_rOut_tendsto (n := n))
    (Filter.Eventually.of_forall
      (complexShrinkingBump_radius_ratio (n := n))) hg
end Ehrhart.DolbeaultRegularity
