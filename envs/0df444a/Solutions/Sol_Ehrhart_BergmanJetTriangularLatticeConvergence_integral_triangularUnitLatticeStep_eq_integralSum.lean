-- Prove2me | solution 1 for Ehrhart.BergmanJetTriangularLatticeConvergence.integral_triangularUnitLatticeStep_eq_integralSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/df8a40cc-3296-4309-9ad2-1833ca507eb5

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
    (∫ x : Space n, triangularUnitLatticeStep B s G k x
      ∂(volume : Measure (Space n))) =
      BoxIntegral.integralSum (s.indicator (G (k + 1)))
        (BoxIntegral.BoxAdditiveMap.toSMul
          (Measure.toBoxAdditive (volume : Measure (Space n))))
        (BoxIntegral.unitPartition.prepartition (k + 1) B) := by
  classical
  unfold triangularUnitLatticeStep
  rw [MeasureTheory.integral_finsetSum]
  · unfold BoxIntegral.integralSum
    apply Finset.sum_congr rfl
    intro J hJ
    rw [MeasureTheory.integral_indicator_const _ J.measurableSet_coe]
    rfl
  · intro J hJ
    exact (integrableOn_const
      (μ := (volume : Measure (Space n)))
      (C := s.indicator (G (k + 1))
        ((BoxIntegral.unitPartition.prepartition (k + 1) B).tag J))
      (BoxIntegral.Box.measure_coe_lt_top J
        (volume : Measure (Space n))).ne).integrable_indicator
      J.measurableSet_coe
end Ehrhart.BergmanJetTriangularLatticeConvergence
