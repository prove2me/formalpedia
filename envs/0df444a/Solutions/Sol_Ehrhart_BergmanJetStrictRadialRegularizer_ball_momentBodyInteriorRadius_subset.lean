-- Prove2me | solution 1 for Ehrhart.BergmanJetStrictRadialRegularizer.ball_momentBodyInteriorRadius_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/189f9fe3-8188-4674-aae9-e568e0a1d4ee

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
    {n : ℕ} (K : CenteredBody n) :
    Metric.ball (0 : Space n)
      (momentBodyInteriorRadius K) ⊆ K.carrier := by
  intro x hx
  exact interior_subset
    (((Metric.isOpen_iff.mp isOpen_interior)
      (0 : Space n) (zero_mem_interior K)).choose_spec.2 hx)
end Ehrhart.BergmanJetStrictRadialRegularizer
