-- Prove2me | solution 1 for Ehrhart.TorusDensityAdaptedWeightedAdjoint.holomorphicCoordinate_complexCoverWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/a745d9f2-24fb-42cd-8eb6-6feb19782774

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_fderiv_complexCoverWeight

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusDensityAdaptedWeightedAdjoint
open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultGraphDistributionBridge WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusDensityAdaptedWeightedAdjoint
theorem _root_.solution
    {n : ℕ} {a : LogSpace n → ℝ}
    (ha : ContDiff ℝ 1 a) (x : LogSpace n) (j : Fin n) :
    holomorphicCoordinate (complexCoverWeight a) x j =
      -complexCoverWeight a x *
        holomorphicCoordinate (fun y => (a y : ℂ)) x j := by
  unfold holomorphicCoordinate
  rw [fderiv_complexCoverWeight ha x (Pi.single j (1 : ℂ)),
    fderiv_complexCoverWeight ha x (Pi.single j Complex.I),
    fderiv_complexOfReal
      (ha.differentiable (by simp)) x (Pi.single j (1 : ℂ)),
    fderiv_complexOfReal
      (ha.differentiable (by simp)) x (Pi.single j Complex.I)]
  ring
end Ehrhart.TorusDensityAdaptedWeightedAdjoint
