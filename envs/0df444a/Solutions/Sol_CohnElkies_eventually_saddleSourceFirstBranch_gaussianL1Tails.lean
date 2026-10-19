-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceFirstBranch_gaussianL1Tails
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/24925e3c-6939-4b36-81b4-931bcbb0e15a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusPolynomial_imaginary_norm_ge_beta
import Theorems.Thm_CohnElkies_minusPolynomial_imaginary_norm_ge_three_beta
import Theorems.Thm_CohnElkies_saddleSourceGaussianPlusIntegrand_tail_norm_eq
import Theorems.Thm_CohnElkies_saddleSourceGaussianMinusIntegrand_tail_norm_eq
import Theorems.Thm_CohnElkies_eventually_saddleSource_firstBranch_uniform_gaussian_tail

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
          ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
            Real.log ℓ / 4 ≤ ℓ * (1 + u) →
              (Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ u) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (saddleSourceFirstBranchCentralRadius ε ℓ u),
                  ‖saddleSourceGaussianPlusIntegrand ε ℓ u T‖) <
                κ * ‖plusPolynomial ε
                  (Complex.I * (u : ℂ))‖) ∧
              (1 + ε / 4 ≤ u →
                Real.sqrt
                    (ℓ * saddleSourceGaussianVariance ε ℓ u) *
                  (∫ T : ℝ in saddleGaussianTailSet
                      (saddleSourceFirstBranchCentralRadius ε ℓ u),
                    ‖saddleSourceGaussianMinusIntegrand ε ℓ u T‖) <
                  κ * ‖minusPolynomial ε
                    (Complex.I * (u : ℂ))‖) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_saddleSource_firstBranch_uniform_gaussian_tail]
    with ε hε htail
  change 0 < ε at hε
  intro κ hκ
  filter_upwards [htail κ hκ]
    with ℓ hℓ
  intro u hu huupper hstar
  let R : ℝ := saddleSourceFirstBranchCentralRadius ε ℓ u
  let s : ℝ :=
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u)
  have hkernel :
      s * (∫ T : ℝ in saddleGaussianTailSet R,
        saddleSourceGaussianKernel ε ℓ u T) < κ := by
    simpa [s, R, saddleSourceFirstBranchCentralRadius] using! hℓ u hu huupper hstar
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
  · intro huminus
    have hden : 0 <
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
