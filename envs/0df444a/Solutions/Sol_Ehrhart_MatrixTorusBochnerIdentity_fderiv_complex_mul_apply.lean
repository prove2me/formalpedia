-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.fderiv_complex_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/a2dd9b88-9c44-4e6e-a128-357f03010548

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    {F G : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ (fun w => F w * G w) z) v =
      F z * (fderiv ℝ G z) v +
        G z * (fderiv ℝ F z) v := by
  have h := congrArg
    (fun A : TorusCharacters.LogSpace n →L[ℝ] ℂ => A v)
    (fderiv_fun_mul (hF z) (hG z))
  simpa [smul_eq_mul] using h
end Ehrhart.MatrixTorusBochnerIdentity
