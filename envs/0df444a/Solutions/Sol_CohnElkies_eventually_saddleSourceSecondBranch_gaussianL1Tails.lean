-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceSecondBranch_gaussianL1Tails
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/4311dcb2-0a41-4c01-87e9-9d0b11d9b56d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusPolynomial_imaginary_norm_ge_beta
import Theorems.Thm_CohnElkies_minusPolynomial_imaginary_norm_ge_three_beta
import Theorems.Thm_CohnElkies_saddleSourceGaussianPlusIntegrand_tail_norm_eq
import Theorems.Thm_CohnElkies_saddleSourceGaussianMinusIntegrand_tail_norm_eq
import Theorems.Thm_CohnElkies_eventually_saddleSource_secondBranch_uniform_gaussian_tail

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
            (Real.sqrt
                (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
              (∫ T : ℝ in saddleGaussianTailSet
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                ‖saddleSourceGaussianPlusIntegrand
                    ε ℓ (1 + δ) T‖) <
              κ * ‖plusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖) ∧
            (Real.sqrt
                (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
              (∫ T : ℝ in saddleGaussianTailSet
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                ‖saddleSourceGaussianMinusIntegrand
                    ε ℓ (1 + δ) T‖) <
              κ * ‖minusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_saddleSource_secondBranch_uniform_gaussian_tail]
    with ε hε htail
  change 0 < ε at hε
  intro κ hκ
  filter_upwards [htail κ hκ]
    with ℓ hℓ
  intro δ hδ
  let u : ℝ := 1 + δ
  let R : ℝ := saddleSourceSecondBranchCentralRadius ε ℓ u
  let s : ℝ :=
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u)
  have hu : -1 < u := by
    try dsimp [u]
    nlinarith
  have huminus : 1 + ε / 4 ≤ u := by
    try dsimp [u]
    nlinarith
  have hkernel :
      s * (∫ T : ℝ in saddleGaussianTailSet R,
        saddleSourceGaussianKernel ε ℓ u T) < κ := by
    simpa [s, R, u, saddleSourceSecondBranchCentralRadius] using! hℓ δ hδ
  constructor
  · have hden : 0 <
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      (beta_pos hε).trans_le
        (plusPolynomial_imaginary_norm_ge_beta hε hu.le)
    change s *
      (∫ T : ℝ in saddleGaussianTailSet R,
        ‖saddleSourceGaussianPlusIntegrand ε ℓ u T‖) <
      κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖
    rw [saddleSourceGaussianPlusIntegrand_tail_norm_eq]
    nlinarith [mul_lt_mul_of_pos_left hkernel hden]
  · have hden : 0 <
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      have hb := beta_pos hε
      have hnorm :=
        minusPolynomial_imaginary_norm_ge_three_beta
          hε huminus
      nlinarith
    change s *
      (∫ T : ℝ in saddleGaussianTailSet R,
        ‖saddleSourceGaussianMinusIntegrand ε ℓ u T‖) <
      κ * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖
    rw [saddleSourceGaussianMinusIntegrand_tail_norm_eq]
    nlinarith [mul_lt_mul_of_pos_left hkernel hden]
end CohnElkies
