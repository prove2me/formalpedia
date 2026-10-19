-- Prove2me | solution 1 for Ehrhart.BergmanJetTriangularLatticeConvergence.triangularUnitLatticeStep_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/6ac0e3e3-0347-46c4-9fb4-362dd6c82183

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTriangularLatticeConvergence
open Set Filter MeasureTheory Metric
open LatticeAsymptotics
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetTriangularLatticeConvergence
theorem _root_.solution {n : ℕ}
    (B : BoxIntegral.Box (Fin n))
    (s : Set (Space n))
    (G : ℕ → Space n → ℝ)
    (k : ℕ) :
    Integrable (triangularUnitLatticeStep B s G k)
      (volume : Measure (Space n)) := by
  classical
  unfold triangularUnitLatticeStep
  apply integrable_finsetSum
  intro J hJ
  exact (integrableOn_const
    (μ := (volume : Measure (Space n)))
    (C := s.indicator (G (k + 1))
      ((BoxIntegral.unitPartition.prepartition (k + 1) B).tag J))
    (BoxIntegral.Box.measure_coe_lt_top J
      (volume : Measure (Space n))).ne).integrable_indicator
    J.measurableSet_coe
end Ehrhart.BergmanJetTriangularLatticeConvergence
