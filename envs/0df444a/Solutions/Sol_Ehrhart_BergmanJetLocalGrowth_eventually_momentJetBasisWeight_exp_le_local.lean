-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.eventually_momentJetBasisWeight_exp_le_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/d7f9e196-2e7d-4e28-804e-82b2ed850156

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceLocalSchwarzRatio_sq_mul_exp_le_one
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_eventually_momentJetBasisRepresentative_local_schwarz

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
      (N : ℕ) (i : Fin (bergmanDimension K k))
      (z : TorusCharacters.LogSpace n)
      (t : ℝ), 0 ≤ t →
        dist z p < R * Real.exp (-t / 2) →
          momentHolomorphicBasisWeight K hk F htransport
            (momentSimultaneousJetBasis K hk F htransport p) z i *
              Real.exp (t *
                (momentTruncatedJetOrder
                  K hk F htransport p N i : ℝ)) ≤
            Real.exp
              ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
                globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n) := by
  filter_upwards
    [eventually_momentJetBasisRepresentative_local_schwarz
      K F htransport p R]
    with k hsch hk N i z t ht hshrink
  let A : ℝ :=
    Real.exp ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
      globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n)
  let q : ℝ := dist z p / R
  let j : ℕ := momentTruncatedJetOrder
    K hk F htransport p N i
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le
        (globalKernelPolynomialConstant_pos K).le)
      (pow_nonneg (Nat.cast_nonneg k) _)
  have hexp : Real.exp (-t / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hball : z ∈ Metric.ball p R := by
    apply Metric.mem_ball.mpr
    have hb := mul_le_mul_of_nonneg_left hexp hR.le
    linarith
  have hsection :
      ‖momentHolomorphicRepresentative K hk F htransport
        (momentSimultaneousJetBasis
          K hk F htransport p i) z‖ ≤
        Real.sqrt A * q ^ j := by
    simpa [A, q, j] using hsch hk N i z hball
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg dist_nonneg hR.le
  have hsq :
      ‖momentHolomorphicRepresentative K hk F htransport
        (momentSimultaneousJetBasis
          K hk F htransport p i) z‖ ^ 2 ≤
        A * (q ^ 2) ^ j := by
    calc
      ‖momentHolomorphicRepresentative K hk F htransport
        (momentSimultaneousJetBasis
          K hk F htransport p i) z‖ ^ 2 ≤
          (Real.sqrt A * q ^ j) ^ 2 :=
            (sq_le_sq₀ (norm_nonneg _)
              (mul_nonneg (Real.sqrt_nonneg _)
                (pow_nonneg hq j))).mpr hsection
      _ = A * (q ^ 2) ^ j := by
        rw [mul_pow, Real.sq_sqrt hA]
        congr 1
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
  have hcontract : q ^ 2 * Real.exp t ≤ 1 :=
    sourceLocalSchwarzRatio_sq_mul_exp_le_one
      dist_nonneg hR hshrink
  have hpow : (q ^ 2 * Real.exp t) ^ j ≤ 1 :=
    pow_le_one₀ (mul_nonneg (sq_nonneg q) (Real.exp_pos _).le)
      hcontract
  change
    Complex.normSq
      (momentHolomorphicRepresentative K hk F htransport
        (momentSimultaneousJetBasis
          K hk F htransport p i) z) *
      Real.exp (t * (j : ℝ)) ≤ A
  rw [Complex.normSq_eq_norm_sq,
    show t * (j : ℝ) = (j : ℝ) * t by ring,
    Real.exp_nat_mul]
  calc
    ‖momentHolomorphicRepresentative K hk F htransport
      (momentSimultaneousJetBasis
        K hk F htransport p i) z‖ ^ 2 * Real.exp t ^ j ≤
        (A * (q ^ 2) ^ j) * Real.exp t ^ j :=
          mul_le_mul_of_nonneg_right hsq
            (pow_nonneg (Real.exp_pos t).le j)
    _ = A * (q ^ 2 * Real.exp t) ^ j := by
      rw [mul_pow]
      ring
    _ ≤ A := by
      nlinarith
end Ehrhart.BergmanJetLocalGrowth
