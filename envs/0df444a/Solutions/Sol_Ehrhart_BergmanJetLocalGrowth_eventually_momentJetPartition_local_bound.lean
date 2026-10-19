-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.eventually_momentJetPartition_local_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/dbf07b35-5f6a-4501-afe2-dfa0d894139c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_eventually_momentJetBasisWeight_exp_le_local

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
          BergmanGeodesicConvexity.exponentialPartition
            (momentHolomorphicBasisWeight K hk F htransport
              (momentSimultaneousJetBasis K hk F htransport p) z)
            (momentTruncatedJetOrder K hk F htransport p N) t ≤
              Real.exp
                ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
                  sourceLocalPolynomialConstant K * (k : ℝ) ^ (3 * n) := by
  have hdim := eventually_bergmanDimension_le_volume_mul_pow K
  filter_upwards
    [eventually_momentJetBasisWeight_exp_le_local
      K F htransport p R hR, hdim]
    with k hweight hkdim hk N z t ht hshrinking
  let A : ℝ :=
    Real.exp ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
      globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le
        (globalKernelPolynomialConstant_pos K).le)
      (pow_nonneg (Nat.cast_nonneg k) _)
  have hsum :
      BergmanGeodesicConvexity.exponentialPartition
        (momentHolomorphicBasisWeight K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p) z)
        (momentTruncatedJetOrder K hk F htransport p N) t ≤
          (bergmanDimension K k : ℝ) * A := by
    unfold BergmanGeodesicConvexity.exponentialPartition
      BergmanGeodesicConvexity.exponentialMoment
    simp only [pow_zero, mul_one]
    calc
      (∑ i, momentHolomorphicBasisWeight K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p) z i *
            Real.exp (t *
              (momentTruncatedJetOrder
                K hk F htransport p N i : ℝ))) ≤
          ∑ _ : Fin (bergmanDimension K k), A := by
            apply Finset.sum_le_sum
            intro i _
            exact hweight hk N i z t ht hshrinking
      _ = (bergmanDimension K k : ℝ) * A := by
            simp
  calc
    BergmanGeodesicConvexity.exponentialPartition
      (momentHolomorphicBasisWeight K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p) z)
      (momentTruncatedJetOrder K hk F htransport p N) t ≤
        (bergmanDimension K k : ℝ) * A := hsum
    _ ≤ ((normalizedVolume K.carrier + 1) *
          (k : ℝ) ^ n) * A :=
            mul_le_mul_of_nonneg_right hkdim hA
    _ = Real.exp
          ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
            sourceLocalPolynomialConstant K * (k : ℝ) ^ (3 * n) := by
      dsimp [A, sourceLocalPolynomialConstant]
      rw [show 3 * n = n + 2 * n by omega, pow_add]
      ring
end Ehrhart.BergmanJetLocalGrowth
