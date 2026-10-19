-- Prove2me | solution 1 for Ehrhart.BergmanJetStrictRadialRegularizer.momentBodyStrictRadialPotential_le_support_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/181c1381-ac57-461f-82c8-59451eddd516

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetStrictRadialRegularizer_momentBodyStrictScale_sum_abs_le_support
import Theorems.Thm_Ehrhart_BergmanJetStrictRadialRegularizer_momentStrictRadialCoordinate_le_abs_add_log_two

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
    momentBodyStrictRadialPotential K x ≤
      supportFunction K.carrier x + (n : ℝ) * Real.log 2 := by
  calc
    momentBodyStrictRadialPotential K x ≤
        ∑ i : Fin n,
          (|momentBodyStrictScale K * x i| + Real.log 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact momentStrictRadialCoordinate_le_abs_add_log_two
        (momentBodyStrictScale K * x i)
    _ = momentBodyStrictScale K * (∑ i : Fin n, |x i|) +
          (n : ℝ) * Real.log 2 := by
      simp_rw [abs_mul,
        abs_of_pos (momentBodyStrictScale_pos K)]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ _ := add_le_add
      (momentBodyStrictScale_sum_abs_le_support K x)
      (le_refl ((n : ℝ) * Real.log 2))
end Ehrhart.BergmanJetStrictRadialRegularizer
