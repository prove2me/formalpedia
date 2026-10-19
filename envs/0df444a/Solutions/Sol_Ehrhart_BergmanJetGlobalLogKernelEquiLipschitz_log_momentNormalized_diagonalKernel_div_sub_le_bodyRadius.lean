-- Prove2me | solution 1 for Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.log_momentNormalized_diagonalKernel_div_sub_le_bodyRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/6d9ba463-5893-4c54-9599-838eebd81db8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_moment_diagonalKernel_le_exp_bodyRadius_mul

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
    (x y : Space n) :
    Real.log
        (diagonalKernel K k (momentNormalizedPotential F) x) /
          (k : ℝ) -
      Real.log
        (diagonalKernel K k (momentNormalizedPotential F) y) /
          (k : ℝ) ≤
      ((n : ℝ) * bodyRadius K) * dist x y := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hx := diagonalKernel_momentNormalized_pos
    K hk F htransport x
  have hy := diagonalKernel_momentNormalized_pos
    K hk F htransport y
  have hratio := moment_diagonalKernel_le_exp_bodyRadius_mul
    K hk F htransport x y
  have hlog := Real.log_le_log hx hratio
  rw [Real.log_mul
    (Real.exp_ne_zero _) hy.ne', Real.log_exp] at hlog
  have hscaled :=
    (div_le_div_iff_of_pos_right hkreal).mpr hlog
  calc
    Real.log
        (diagonalKernel K k (momentNormalizedPotential F) x) /
          (k : ℝ) -
      Real.log
        (diagonalKernel K k (momentNormalizedPotential F) y) /
          (k : ℝ) ≤
      (((k : ℝ) *
            (((n : ℝ) * bodyRadius K) * dist x y) +
          Real.log
            (diagonalKernel K k
              (momentNormalizedPotential F) y)) /
            (k : ℝ)) -
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) y) /
            (k : ℝ) := by linarith
    _ = ((n : ℝ) * bodyRadius K) * dist x y := by
      field_simp
      ; ring
end Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
