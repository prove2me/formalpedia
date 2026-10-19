-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerCore.sourceTorusFormFullDerivativeDensity_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/f01cf308-e068-406a-b884-850ebb781967

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerCore
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity
open ComplexMatrixWeightedHilbert MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerCore
theorem _root_.solution
    {n : ℕ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (p : WeightedTorusHilbert.LogTorus n) :
    0 ≤ (sourceTorusFormFullDerivativeDensity W p).re := by
  unfold sourceTorusFormFullDerivativeDensity
  simp_rw [Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]
  exact Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ =>
      Complex.normSq_nonneg
        (sourceTorusBarPartial (fun z => W z i) j p)))
end Ehrhart.MatrixTorusBochnerCore
