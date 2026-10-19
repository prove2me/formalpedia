-- Prove2me | solution 1 for Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.moment_diagonalTerm_le_exp_bodyRadius_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/22ba86f4-bb43-4026-ab8c-5ccb6f614838

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_monomial_pairing_sub_le_bodyRadius

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
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    (x y : Space n) :
    diagonalTerm K k (momentNormalizedPotential F) u x ≤
      Real.exp
          ((k : ℝ) *
            (((n : ℝ) * bodyRadius K) * dist x y)) *
        diagonalTerm K k (momentNormalizedPotential F) u y := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hpair := monomial_pairing_sub_le_bodyRadius K u x y
  have hnorm := momentMonomialNormSquared_pos
    K hk F htransport u
  have hexp :
      Real.exp ((k : ℝ) * pairing (u : Space n) x) ≤
        Real.exp
          ((k : ℝ) *
            (((n : ℝ) * bodyRadius K) * dist x y)) *
          Real.exp ((k : ℝ) * pairing (u : Space n) y) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold diagonalTerm
  calc
    Real.exp ((k : ℝ) * pairing (u : Space n) x) /
        monomialNormSquared k (u : Space n)
          (momentNormalizedPotential F) ≤
      (Real.exp
          ((k : ℝ) *
            (((n : ℝ) * bodyRadius K) * dist x y)) *
        Real.exp ((k : ℝ) * pairing (u : Space n) y)) /
          monomialNormSquared k (u : Space n)
            (momentNormalizedPotential F) :=
      (div_le_div_iff_of_pos_right hnorm).mpr hexp
    _ = Real.exp
          ((k : ℝ) *
            (((n : ℝ) * bodyRadius K) * dist x y)) *
        (Real.exp ((k : ℝ) * pairing (u : Space n) y) /
          monomialNormSquared k (u : Space n)
            (momentNormalizedPotential F)) := by
      ring
end Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
