-- Prove2me | solution 1 for Ehrhart.BergmanJetStrictRadialRegularizer.momentStrictRadialCoordinate_le_abs_add_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/8582e687-b4d8-453d-a279-8921a37072b9

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    (y : ℝ) :
    momentStrictRadialCoordinate y ≤ |y| + Real.log 2 := by
  have hpos : Real.exp y ≤ Real.exp |y| :=
    Real.exp_le_exp.mpr (le_abs_self y)
  have hnegarg : -y ≤ |y| := by
    calc
      -y ≤ |-y| := le_abs_self (-y)
      _ = |y| := abs_neg y
  have hneg : Real.exp (-y) ≤ Real.exp |y| :=
    Real.exp_le_exp.mpr hnegarg
  have hsum : Real.exp y + Real.exp (-y) ≤
      2 * Real.exp |y| := by linarith
  calc
    momentStrictRadialCoordinate y =
        Real.log (Real.exp y + Real.exp (-y)) := rfl
    _ ≤ Real.log (2 * Real.exp |y|) := by
      exact Real.strictMonoOn_log.monotoneOn
        (show Real.exp y + Real.exp (-y) ∈ Set.Ioi (0 : ℝ) from
          momentStrictRadialCoordinate_denominator_pos y)
        (show 2 * Real.exp |y| ∈ Set.Ioi (0 : ℝ) from
          mul_pos (by norm_num : (0 : ℝ) < 2) (Real.exp_pos |y|))
        hsum
    _ = |y| + Real.log 2 := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (Real.exp_ne_zero |y|), Real.log_exp]
      ring
end Ehrhart.BergmanJetStrictRadialRegularizer
