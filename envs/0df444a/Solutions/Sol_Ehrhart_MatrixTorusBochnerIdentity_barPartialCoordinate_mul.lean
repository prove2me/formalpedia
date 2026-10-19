-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.barPartialCoordinate_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/ec460fe9-c90c-4e54-8f10-5039e2a69e3c

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
    barPartialCoordinate (fun w => F w * G w) z j =
      F z * barPartialCoordinate G z j +
        G z * barPartialCoordinate F z j := by
  unfold barPartialCoordinate
  rw [fderiv_complex_mul_apply hF hG z (Pi.single j (1 : ℂ)),
    fderiv_complex_mul_apply hF hG z (Pi.single j Complex.I)]
  ring
end Ehrhart.MatrixTorusBochnerIdentity
