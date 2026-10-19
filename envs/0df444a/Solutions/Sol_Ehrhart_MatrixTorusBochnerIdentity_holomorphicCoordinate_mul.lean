-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.holomorphicCoordinate_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/8b7d492c-033f-4d6e-8e07-6f7176d76a84

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_fderiv_complex_mul_apply

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
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    holomorphicCoordinate (fun w => F w * G w) z j =
      F z * holomorphicCoordinate G z j +
        G z * holomorphicCoordinate F z j := by
  unfold holomorphicCoordinate
  rw [fderiv_complex_mul_apply hF hG z (Pi.single j (1 : ℂ)),
    fderiv_complex_mul_apply hF hG z (Pi.single j Complex.I)]
  ring
end Ehrhart.MatrixTorusBochnerIdentity
