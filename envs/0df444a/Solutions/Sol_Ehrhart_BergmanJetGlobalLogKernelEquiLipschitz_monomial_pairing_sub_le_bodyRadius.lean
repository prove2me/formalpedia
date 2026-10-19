-- Prove2me | solution 1 for Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.monomial_pairing_sub_le_bodyRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/553ecad0-4598-4aa3-a6c4-1b25afd3c2f8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics BergmanMonomials LatticeAsymptotics LaurentJetSeparatedness
open GlobalBergmanKernelBound MomentMinimizer MomentOptimizer MomentTargetGeodesic
open MomentFirstVariation MomentRegularity BergmanJetBasis MomentWeakGlobalKernel
open BergmanJetPointwiseLogKernel
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n)
    (u : monomialIndex K k)
    (x y : Space n) :
    pairing (u : Space n) x -
        pairing (u : Space n) y ≤
      ((n : ℝ) * bodyRadius K) * dist x y := by
  have hu := monomialExponent_norm_le_bodyRadius K u
  have hp := MonomialDivergence.abs_pairing_le_dimension_mul_norm
    (u : Space n) (x - y)
  calc
    pairing (u : Space n) x -
        pairing (u : Space n) y =
      pairing (u : Space n) (x - y) := by
        simp [pairing, mul_sub, Finset.sum_sub_distrib]
    _ ≤ |pairing (u : Space n) (x - y)| :=
      le_abs_self _
    _ ≤ ((n : ℝ) * ‖(u : Space n)‖) * ‖x - y‖ := hp
    _ ≤ ((n : ℝ) * bodyRadius K) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg n))
        (norm_nonneg _)
    _ = ((n : ℝ) * bodyRadius K) * dist x y := by
      rw [dist_eq_norm]
end Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
