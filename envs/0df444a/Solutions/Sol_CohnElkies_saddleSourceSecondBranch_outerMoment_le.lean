-- Prove2me | solution 1 for CohnElkies.saddleSourceSecondBranch_outerMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/66232e42-bf41-44e4-a279-7fcd8fb956a7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSecondBranch_gammaWeightedCoefficient_le
import Theorems.Thm_CohnElkies_saddleSecondBranch_linearWeightedCoefficient_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ δ : ℝ} (hℓ : 1 ≤ ℓ) (hδ : 0 ≤ δ) :
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
        saddleSourceSecondBranchMomentCoefficient *
          (2 + δ) ^ 4 := by
  let C : ℝ := 8 * Real.exp 1
  let η : ℝ := 2 + δ
  let q : ℝ := saddleSourceSecondBranchGammaGaussianRate ℓ δ
  let a : ℝ := saddleSourceSecondBranchGammaLinearRate ℓ
  have hℓpositive : 0 < ℓ := by linarith
  have hη : 1 ≤ η := by
    try dsimp [η]
    linarith
  have hηpositive : 0 < η := by linarith
  have hC : 0 < C := by
    try dsimp [C]
    positivity
  have hq : 0 < q := by
    try dsimp [q, saddleSourceSecondBranchGammaGaussianRate]
    positivity
  have ha : 0 < a := by
    try dsimp [a, saddleSourceSecondBranchGammaLinearRate]
    positivity
  have hqrate : 1 / q ≤ C * η := by
    calc
      1 / q = (C * η) / ℓ := by
        try dsimp [q, C, η,
          saddleSourceSecondBranchGammaGaussianRate]
        field_simp [hℓpositive.ne',
          (Real.exp_pos 1).ne', hηpositive.ne']
      _ ≤ C * η := by
        apply (div_le_iff₀ hℓpositive).2
        nlinarith [mul_nonneg
          (mul_nonneg hC.le hηpositive.le)
          (show 0 ≤ ℓ - 1 by linarith)]
  have harate : 1 / a ≤ C := by
    calc
      1 / a = C / ℓ := by
        try dsimp [a, C,
          saddleSourceSecondBranchGammaLinearRate]
        field_simp [hℓpositive.ne',
          (Real.exp_pos 1).ne']
      _ ≤ C := by
        apply (div_le_iff₀ hℓpositive).2
        nlinarith [mul_nonneg hC.le
          (show 0 ≤ ℓ - 1 by linarith)]
  have hgamma := saddleSecondBranch_gammaWeightedCoefficient_le
    hq hη hC hqrate
  have hlinear := saddleSecondBranch_linearWeightedCoefficient_le
    ha hη hC harate
  change
    2 * max (1 : ℝ) ((Real.sqrt (q / 6) ^ 3)⁻¹) *
          Real.sqrt (Real.pi / (q / 2)) +
      2 * max (1 : ℝ) (((a / 6) ^ 3)⁻¹) *
          (2 / (a / 2)) ≤
        saddleSourceSecondBranchMomentCoefficient * η ^ 4
  unfold saddleSourceSecondBranchMomentCoefficient
  change
    2 * max (1 : ℝ) ((Real.sqrt (q / 6) ^ 3)⁻¹) *
          Real.sqrt (Real.pi / (q / 2)) +
      2 * max (1 : ℝ) (((a / 6) ^ 3)⁻¹) *
          (2 / (a / 2)) ≤
      (2 * (1 + (6 * C) ^ 3) *
          (1 + 2 * Real.pi * C) +
        8 * C * (1 + (6 * C) ^ 3)) * η ^ 4
  nlinarith
end CohnElkies
