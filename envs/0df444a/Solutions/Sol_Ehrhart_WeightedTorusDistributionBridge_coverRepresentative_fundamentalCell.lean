-- Prove2me | solution 1 for Ehrhart.WeightedTorusDistributionBridge.coverRepresentative_fundamentalCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/d6a72354-757b-4000-bd44-cf60dcf54171

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_coverRepresentative_coe
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_angularFundamentalEquiv_symm_apply

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusDistributionBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
attribute [local instance] Ehrhart.WeightedTorusDistributionBridge._p2m_local_instance_3610026555_18903
attribute [local instance] Ehrhart.WeightedTorusDistributionBridge._p2m_local_instance_3610026555_18906
namespace Ehrhart.WeightedTorusDistributionBridge
theorem _root_.solution {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (x : Space n)
    (t : angularFundamentalCell n) :
    JointHolomorphicLaurentFourierCompatibility.coverRepresentative
      F x ((angularFundamentalEquiv n).symm t) =
      F (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t.1) := by
  rw [angularFundamentalEquiv_symm_apply]
  apply JointHolomorphicLaurentFourierCompatibility.coverRepresentative_coe
  intro i hi
  simpa using t.property i
end Ehrhart.WeightedTorusDistributionBridge
