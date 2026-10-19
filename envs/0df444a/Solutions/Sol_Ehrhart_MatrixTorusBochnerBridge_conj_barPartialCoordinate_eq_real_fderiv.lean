-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.conj_barPartialCoordinate_eq_real_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/2a878422-5f30-4221-9c6a-353e01d2e710

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_fderiv_conj

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerBridge
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerBridge
theorem _root_.solution
    {n : ℕ}
    {G : TorusCharacters.LogSpace n → ℂ}
    (hG : ContDiff ℝ 1 G)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    conj (barPartialCoordinate G z j) =
      ((fderiv ℝ (fun w => conj (G w)) z)
          (Pi.single j (1 : ℂ)) -
        Complex.I *
          (fderiv ℝ (fun w => conj (G w)) z)
            (Pi.single j Complex.I)) / 2 := by
  rw [fderiv_conj (hG.differentiable (by simp)) z
    (Pi.single j (1 : ℂ)),
    fderiv_conj (hG.differentiable (by simp)) z
      (Pi.single j Complex.I)]
  unfold barPartialCoordinate
  simp only [map_div₀, map_add, map_mul,
    Complex.conj_I, map_ofNat]
  ring
end Ehrhart.MatrixTorusBochnerBridge
