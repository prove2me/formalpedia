-- Prove2me | solution 1 for CohnElkies.eventually_saddleSource_secondBranch_uniform_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/08d3255d-6597-4a2f-b99b-1bc8859b552e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_saddleGaussianOuterPhi_uniform_polynomial
import Theorems.Thm_CohnElkies_saddleSourceSecondBranchVarianceFloor_pos
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_secondBranch_floor
import Theorems.Thm_CohnElkies_eventually_saddleSource_secondBranch_normalized_tail_bound
import Theorems.Thm_CohnElkies_saddleSourceSecondBranchMomentCoefficient_pos
import Theorems.Thm_CohnElkies_saddleSourceSecondBranch_outerMoment_le
import Theorems.Thm_CohnElkies_saddleSourceSecondBranchVarianceCoefficient_pos
import Theorems.Thm_CohnElkies_eventually_saddleSource_secondBranch_sqrtVariance_le
import Theorems.Thm_CohnElkies_tendsto_saddleSourceSecondBranchLocalTailMajorant

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ δ : ℝ, ε / 2 ≤ δ →
            Real.sqrt
                (ℓ * saddleSourceGaussianVariance
                  ε ℓ (1 + δ)) *
              (∫ T : ℝ in saddleGaussianTailSet
                  (ℓ ^ (1 / 12 : ℝ) /
                    Real.sqrt
                      (ℓ * saddleSourceGaussianVariance
                        ε ℓ (1 + δ))),
                saddleGaussianTailWeight T *
                  Real.exp
                    (-saddleSourceContourDamping
                      ε ℓ (1 + δ) T)) < κ := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_saddleSource_secondBranch_normalized_tail_bound,
      eventually_saddleSource_secondBranch_sqrtVariance_le,
      eventually_saddleSourceGaussianVariance_secondBranch_floor]
    with ε hε htail hsqrt hfloor
  change 0 < ε at hε
  intro κ hκ
  let B : ℝ := shellLocation ε
  let Q : ℝ := shellWeight ε
  let t₀ : ℝ := saddleSourceSecondBranchLocalFrequency ε
  let c : ℝ := (99 / 5000 : ℝ) * t₀ ^ 2
  let V₀ : ℝ := saddleSourceSecondBranchVarianceFloor ε
  let C : ℝ := saddleSourceSecondBranchVarianceCoefficient ε
  let K : ℝ :=
    Real.sqrt C * saddleSourceSecondBranchMomentCoefficient
  have hB : 0 < B := by
    try dsimp [B, shellLocation]
    positivity
  have hQ : 0 < Q := by
    try dsimp [Q]
    exact shellWeight_pos ε
  have ht₀ : 0 < t₀ := by
    try dsimp [t₀, saddleSourceSecondBranchLocalFrequency, B]
    positivity
  have hc : 0 < c := by
    try dsimp [c]
    positivity
  have hV₀ : 0 < V₀ := by
    try dsimp [V₀]
    exact saddleSourceSecondBranchVarianceFloor_pos hε
  have hC : 0 < C := by
    try dsimp [C]
    exact saddleSourceSecondBranchVarianceCoefficient_pos ε
  have hK : 0 < K := by
    try dsimp [K]
    exact mul_pos (Real.sqrt_pos.2 hC)
      saddleSourceSecondBranchMomentCoefficient_pos
  have hhalf : 0 < κ / 2 := by positivity
  have houter :=
    eventually_saddleGaussianOuterPhi_uniform_polynomial
      hB hQ hc (by positivity : 0 ≤ ε / 2)
        hK.le (κ / 2) hhalf
  have hlocal :=
    tendsto_saddleSourceSecondBranchLocalTailMajorant.eventually
      (Iio_mem_nhds hhalf)
  filter_upwards
    [eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop
        ((600 * Real.exp 1) / V₀),
      hlocal, houter]
    with ℓ hℓ hone hlocalℓ houterℓ
  intro δ hδ
  let V : ℝ := saddleSourceGaussianVariance ε ℓ (1 + δ)
  let z : ℝ := ℓ ^ (1 / 12 : ℝ)
  let η : ℝ := 2 + δ
  have hℓpositive : 0 < ℓ := by linarith
  have hδ0 : 0 ≤ δ := by nlinarith
  have hη : 1 ≤ η := by
    try dsimp [η]
    linarith
  have hVfloor : V₀ ≤ V := by
    try dsimp [V₀, V]
    exact hfloor ℓ hℓpositive δ hδ
  have hV : 0 < V := hV₀.trans_le hVfloor
  have hz : 0 ≤ z := by
    try dsimp [z]
    positivity
  have hscale : 600 * Real.exp 1 ≤ ℓ * V₀ := by
    have h := (div_le_iff₀ hV₀).mp hone
    nlinarith
  have hfullscale : 600 * Real.exp 1 ≤ ℓ * V := by
    have h := mul_le_mul_of_nonneg_left
      hVfloor hℓpositive.le
    linarith
  have hk :
      6 ≤ saddleSourceSecondBranchGaussianRate ε ℓ δ := by
    unfold saddleSourceSecondBranchGaussianRate
    change 6 ≤ (ℓ / (100 * Real.exp 1)) * V
    have hden : (0 : ℝ) < 100 * Real.exp 1 := by
      positivity
    have hgoal :
        (6 : ℝ) ≤ (ℓ * V) / (100 * Real.exp 1) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    convert! hgoal using 1; ring
  have hsource := htail ℓ hℓpositive δ hδ z hz hk
  have hpower : z ^ 2 = ℓ ^ (1 / 6 : ℝ) := by
    try dsimp [z]
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul hℓpositive.le]
    congr 1
    norm_num
  have hlocalterm :
      2 * Real.sqrt (400 * Real.exp 1 * Real.pi) *
        Real.exp
          (-(z ^ 2 / (400 * Real.exp 1))) < κ / 2 := by
    rw [hpower]
    exact hlocalℓ
  have hsqrtsource :
      Real.sqrt (ℓ * V) ≤
        Real.sqrt C * Real.sqrt ℓ *
          Real.exp (((B + 1) / 2) * δ) := by
    simpa [V, C, B] using! hsqrt ℓ hℓ δ hδ
  have hmoment :=
    saddleSourceSecondBranch_outerMoment_le hℓ hδ0
  have hmoment' :
      2 * max (1 : ℝ)
          ((Real.sqrt
            (saddleSourceSecondBranchGammaGaussianRate
              ℓ δ / 6) ^ 3)⁻¹) *
            Real.sqrt
              (Real.pi /
                (saddleSourceSecondBranchGammaGaussianRate
                  ℓ δ / 2)) +
        2 * max (1 : ℝ)
          (((saddleSourceSecondBranchGammaLinearRate
            ℓ / 6) ^ 3)⁻¹) *
            (2 /
              (saddleSourceSecondBranchGammaLinearRate
                ℓ / 2)) ≤
          saddleSourceSecondBranchMomentCoefficient * η ^ 4 := by
    simpa [η] using! hmoment
  have hqpositive :
      0 < saddleSourceSecondBranchGammaGaussianRate ℓ δ := by
    unfold saddleSourceSecondBranchGammaGaussianRate
    positivity
  have hapositive :
      0 < saddleSourceSecondBranchGammaLinearRate ℓ := by
    unfold saddleSourceSecondBranchGammaLinearRate
    positivity
  have hmomentnonnegative :
      0 ≤
        2 * max (1 : ℝ)
            ((Real.sqrt
              (saddleSourceSecondBranchGammaGaussianRate
                ℓ δ / 6) ^ 3)⁻¹) *
              Real.sqrt
                (Real.pi /
                  (saddleSourceSecondBranchGammaGaussianRate
                    ℓ δ / 2)) +
          2 * max (1 : ℝ)
            (((saddleSourceSecondBranchGammaLinearRate
              ℓ / 6) ^ 3)⁻¹) *
              (2 /
                (saddleSourceSecondBranchGammaLinearRate
                  ℓ / 2)) := by
    positivity
  have hbarrier :
      saddleSourceSecondBranchOuterBarrier ε ℓ δ =
        c * ℓ * Q * Real.exp (B * δ) := by
    try dsimp [saddleSourceSecondBranchOuterBarrier,
      c, Q, B, t₀]
    ring_nf
  have houterterm :
      Real.sqrt (ℓ * V) *
          Real.exp
            (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
            (2 * max (1 : ℝ)
              ((Real.sqrt
                (saddleSourceSecondBranchGammaGaussianRate
                  ℓ δ / 6) ^ 3)⁻¹) *
                Real.sqrt
                  (Real.pi /
                    (saddleSourceSecondBranchGammaGaussianRate
                      ℓ δ / 2)) +
              2 * max (1 : ℝ)
                (((saddleSourceSecondBranchGammaLinearRate
                  ℓ / 6) ^ 3)⁻¹) *
                  (2 /
                    (saddleSourceSecondBranchGammaLinearRate
                      ℓ / 2))) < κ / 2 := by
    calc
      Real.sqrt (ℓ * V) *
          Real.exp
            (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
            (2 * max (1 : ℝ)
              ((Real.sqrt
                (saddleSourceSecondBranchGammaGaussianRate
                  ℓ δ / 6) ^ 3)⁻¹) *
                Real.sqrt
                  (Real.pi /
                    (saddleSourceSecondBranchGammaGaussianRate
                      ℓ δ / 2)) +
              2 * max (1 : ℝ)
                (((saddleSourceSecondBranchGammaLinearRate
                  ℓ / 6) ^ 3)⁻¹) *
                  (2 /
                    (saddleSourceSecondBranchGammaLinearRate
                      ℓ / 2))) ≤
        (Real.sqrt C * Real.sqrt ℓ *
          Real.exp (((B + 1) / 2) * δ)) *
          Real.exp
            (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
              (saddleSourceSecondBranchMomentCoefficient *
                η ^ 4) := by
          gcongr
      _ = K * Real.sqrt ℓ *
          Real.exp (((B + 1) / 2) * δ) *
          (2 + δ) ^ 4 *
          Real.exp
            (-c * ℓ * Q * Real.exp (B * δ)) := by
          rw [hbarrier]
          try dsimp [K, η]
          ring_nf
      _ < κ / 2 := houterℓ δ hδ
  change
    Real.sqrt (ℓ * V) *
      (∫ T : ℝ in saddleGaussianTailSet
          (z / Real.sqrt (ℓ * V)),
        saddleGaussianTailWeight T *
          Real.exp
            (-saddleSourceContourDamping
              ε ℓ (1 + δ) T)) < κ
  change
    Real.sqrt (ℓ * V) *
      (∫ T : ℝ in saddleGaussianTailSet
          (z / Real.sqrt (ℓ * V)),
        saddleGaussianTailWeight T *
          Real.exp
            (-saddleSourceContourDamping
              ε ℓ (1 + δ) T)) ≤ _ at hsource
  nlinarith
end CohnElkies
