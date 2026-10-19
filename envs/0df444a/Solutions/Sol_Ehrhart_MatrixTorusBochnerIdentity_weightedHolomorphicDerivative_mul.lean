-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.weightedHolomorphicDerivative_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/a59d7a98-86bb-4d84-ae50-83c30301ed7d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_holomorphicCoordinate_mul

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerIdentity
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerIdentity
theorem _root_.solution
    {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    {F G : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    weightedHolomorphicDerivative a
      (fun w => F w * G w) j z =
      F z * weightedHolomorphicDerivative a G j z +
        G z * holomorphicCoordinate F z j := by
  unfold weightedHolomorphicDerivative
  rw [holomorphicCoordinate_mul hF hG z j]
  ring
end Ehrhart.MatrixTorusBochnerIdentity
