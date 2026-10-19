-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.eventually_momentJetGeodesic_local_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/56fc3427-ebeb-4de9-9dfb-ea43c7ad388d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceLocalPolynomialConstant_pos
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_eventually_momentJetPartition_local_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetLocalGrowth
open Set Function Filter MeasureTheory Module Metric Asymptotics
open BergmanMonomials BergmanDiagonalBasisIndependence GlobalBergmanKernelBound AdaptedBergmanBasis
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetBasis MomentWeakGlobalKernel BergmanJetGeodesic BergmanJetProfileBridge
open BergmanJetRealGeodesic JetEnvelopeLocalGrowth LaurentJetMultiplicityBridge
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace Ehrhart.BergmanJetLocalGrowth
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (R : ℝ) (hR : 0 < R) :
    ∀ᶠ k : ℕ in atTop, ∀ (hk : 0 < k)
      (N : ℕ) (z : TorusCharacters.LogSpace n)
      (t : ℝ), 0 ≤ t →
        dist z p < R * Real.exp (-t / 2) →
          momentJetGeodesic K hk F htransport p N z t ≤
            momentLocalPotentialMaximum K F p R +
              sourceLocalKernelLogError K k := by
  filter_upwards
    [eventually_momentJetPartition_local_bound
      K F htransport p R hR]
    with k hbound hk N z t ht hshrinking
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hconstant := sourceLocalPolynomialConstant_pos K
  have hpart : 0 <
      BergmanGeodesicConvexity.exponentialPartition
        (momentHolomorphicBasisWeight K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p) z)
        (momentTruncatedJetOrder K hk F htransport p N) t :=
    BergmanGeodesicConvexity.exponentialPartition_pos _ _
      (momentHolomorphicBasisWeight_nonneg K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p) z)
      (exists_positive_momentHolomorphicBasisWeight
        K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p) z) t
  have hmajor : 0 <
      Real.exp ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
        sourceLocalPolynomialConstant K * (k : ℝ) ^ (3 * n) := by
    positivity
  have hlog := Real.strictMonoOn_log.monotoneOn
    hpart hmajor (hbound hk N z t ht hshrinking)
  have hexpand :
      Real.log
        (Real.exp ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
          sourceLocalPolynomialConstant K * (k : ℝ) ^ (3 * n)) =
        (k : ℝ) * momentLocalPotentialMaximum K F p R +
          Real.log (sourceLocalPolynomialConstant K) +
            3 * (n : ℝ) * Real.log (k : ℝ) := by
    rw [Real.log_mul
      (mul_ne_zero (Real.exp_ne_zero _) (ne_of_gt hconstant))
        (pow_ne_zero _ (ne_of_gt hkreal)),
      Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hconstant),
      Real.log_exp, Real.log_pow]
    push_cast
    ring
  rw [hexpand] at hlog
  unfold momentJetGeodesic
    BergmanGeodesicConvexity.logarithmicPotential
    sourceLocalKernelLogError
  apply (div_le_iff₀ hkreal).mpr
  calc
    Real.log
      (BergmanGeodesicConvexity.exponentialPartition
        (momentHolomorphicBasisWeight K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p) z)
        (momentTruncatedJetOrder K hk F htransport p N) t) ≤
          (k : ℝ) * momentLocalPotentialMaximum K F p R +
            Real.log (sourceLocalPolynomialConstant K) +
              3 * (n : ℝ) * Real.log (k : ℝ) := hlog
    _ = (momentLocalPotentialMaximum K F p R +
          (Real.log (sourceLocalPolynomialConstant K) +
            3 * (n : ℝ) * Real.log (k : ℝ)) / (k : ℝ)) *
          (k : ℝ) := by
      field_simp
      ring
end Ehrhart.BergmanJetLocalGrowth
