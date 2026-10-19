-- Prove2me | solution 1 for Ehrhart.BergmanJetStrictRadialRegularizer.momentBodyStrictScale_sum_abs_le_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/f09cf209-4f25-439d-8964-508f477eedc0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetStrictRadialRegularizer_ball_momentBodyInteriorRadius_subset

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetStrictRadialRegularizer
open Set Function Filter MeasureTheory Matrix
open TorusCharacters SupportFunction LatticeAsymptotics BergmanAsymptotics
open ComplexMatrixWeightedHilbert MatrixTorusBochnerBridge MatrixTorusBochnerCore
open WeightedDolbeaultBochnerIdentity SchurConvexity
open scoped BigOperators ENNReal Topology ContDiff MatrixOrder
  ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
namespace Ehrhart.BergmanJetStrictRadialRegularizer
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) :
    momentBodyStrictScale K * (∑ i : Fin n, |x i|) ≤
      supportFunction K.carrier x := by
  let c : ℝ := momentBodyStrictScale K
  have hc : 0 < c := momentBodyStrictScale_pos K
  have hnorm : ‖c • signVector x‖ ≤ c := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    exact mul_le_of_le_one_right hc.le (norm_signVector_le_one x)
  have hradius : c < momentBodyInteriorRadius K := by
    exact half_lt_self (momentBodyInteriorRadius_pos K)
  have hball : c • signVector x ∈
      Metric.ball (0 : Space n)
        (momentBodyInteriorRadius K) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hnorm.trans_lt hradius
  have hmem := ball_momentBodyInteriorRadius_subset K hball
  have hs := pairing_le_supportFunction K.compact hmem x
  rw [pairing_smul_left, pairing_signVector] at hs
  exact hs
end Ehrhart.BergmanJetStrictRadialRegularizer
