-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.integral_unweightedSourceTorusIntegrand_eq_weighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/3c2477dd-b0ba-4adf-9557-c33db33fbdbf

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_radialWeight_lt_top

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
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    (f : WeightedTorusHilbert.LogTorus n → ℂ) :
    (∫ p : WeightedTorusHilbert.LogTorus n,
      unweightedSourceTorusIntegrand φ f p
      ∂((volume : Measure (Space n)).prod
        (angularMeasure n))) =
    ∫ p : WeightedTorusHilbert.LogTorus n,
      f p ∂(weightedTorusMeasure 1 φ) := by
  have hd : Measurable
      (fun p : WeightedTorusHilbert.LogTorus n =>
        radialWeight 1 φ p.1) :=
    (radialWeight_measurable 1 hφ).comp measurable_fst
  rw [weightedTorusMeasure_eq_withDensity 1 hφ,
    integral_withDensity_eq_integral_toReal_smul
      hd (Filter.Eventually.of_forall
        (fun p : WeightedTorusHilbert.LogTorus n =>
          radialWeight_lt_top φ p.1))]
  apply integral_congr_ae
  filter_upwards [] with p
  unfold unweightedSourceTorusIntegrand radialWeight
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Complex.real_smul]
  norm_num
end Ehrhart.MatrixTorusBochnerBridge
