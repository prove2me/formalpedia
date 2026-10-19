-- Prove2me | solution 1 for Ehrhart.TorusWeightedDensityConvolutionDivergence.normalizedCoverMollification_eq_kernel_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/6533ccee-646b-4c08-abdc-888870be3290

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultRegularity_complexRealMultiplication_apply

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeightedDensityConvolutionDivergence
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters DolbeaultRegularity
open DolbeaultGraphDistributionBridge WeightedDolbeaultBochnerIdentity
open TorusWeakDolbeaultMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusWeightedDensityConvolutionDivergence
theorem _root_.solution
    {n : ℕ} (g : LogSpace n → ℂ)
    (k : ℕ) (x : LogSpace n) :
    normalizedCoverMollification g k x =
      ∫ y : LogSpace n,
        g y *
          ((complexShrinkingBump (n := n) k).normed
            (volume : Measure (LogSpace n)) (x - y) : ℂ)
        ∂(volume : Measure (LogSpace n)) := by
  unfold normalizedCoverMollification
  rw [← complex_convolution_flip,
    MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [complexRealMultiplication_apply, mul_comm]
end Ehrhart.TorusWeightedDensityConvolutionDivergence
