-- Prove2me | solution 1 for Ehrhart.MatrixTorusDolbeaultGraph.angularMatrixSquareRoot_posDef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/5bc7f72c-3428-4073-b59d-e8dd09b643f1

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusDolbeaultGraph
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusMatrixSquareRootContinuity
open scoped BigOperators ENNReal InnerProductSpace Topology
  MatrixOrder ComplexOrder ComplexConjugate
  Matrix.Norms.L2Operator ContDiff
namespace Ehrhart.MatrixTorusDolbeaultGraph
theorem _root_.solution {n : ℕ}
    {H : LogTorus n → Matrix (Fin n) (Fin n) ℂ}
    (hH : ∀ q, (H q).PosDef) (q : LogTorus n) :
    (angularMatrixSquareRoot H q).PosDef := by
  exact (hH q).isStrictlyPositive.sqrt.posDef
end Ehrhart.MatrixTorusDolbeaultGraph
