-- Prove2me | solution 1 for Ehrhart.BergmanJetTriangularLatticeConvergence.integral_triangularUnitLatticeStep_eq_lattice_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/0c4eadb9-b81c-4af5-92d4-ac5c436b5455

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTriangularLatticeConvergence_integral_triangularUnitLatticeStep_eq_integralSum

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
    (hB : BoxIntegral.hasIntegralVertices B)
    (s : Set (Space n))
    (hs : s ⊆ (B : Set (Space n)))
    (G : ℕ → Space n → ℝ)
    (k : ℕ) :
    (∫ x : Space n, triangularUnitLatticeStep B s G k x
      ∂(volume : Measure (Space n))) =
      (∑' x : ↑(s ∩ scaledIntegerLattice n (k + 1)), G (k + 1) x) /
        ((k + 1 : ℕ) : ℝ) ^ n := by
  rw [integral_triangularUnitLatticeStep_eq_integralSum]
  simpa [scaledIntegerLattice] using
    (BoxIntegral.unitPartition.integralSum_eq_tsum_div
      (n := k + 1) s (G (k + 1)) hB hs)
end Ehrhart.BergmanJetTriangularLatticeConvergence
