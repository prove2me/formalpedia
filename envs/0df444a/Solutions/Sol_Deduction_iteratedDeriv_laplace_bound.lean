-- Prove2me | solution 1 for Deduction.iteratedDeriv_laplace_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:19.040073+00:00
-- url     : https://prove2.me/submissions/0fac527c-466c-40b5-818b-4b0989530d9e

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_IteratedDerivLaplace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution (g : ℝ → ℝ) (C : ℝ)
    (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)) (k : ℕ) (b : ℝ) (z : ℂ) (hz : 2 + b ≤ z.re)
    (u : ℝ) (hu : 0 < u) :
    ‖(g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u)‖ ≤ C * (u ^ k * Real.exp (-b * u)) := by
  have h1 : ‖(g u : ℂ)‖ ≤ C * Real.exp (2 * u) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hgC u hu.le
  have h2 : ‖((-u : ℝ) : ℂ) ^ k‖ = u ^ k := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hu]
  have h3 : ‖cexp (-z * u)‖ ≤ Real.exp (-(2 + b) * u) := by
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_im, mul_zero, sub_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hC : 0 ≤ C * Real.exp (2 * u) := le_trans (norm_nonneg _) h1
  rw [norm_mul, norm_mul, h2]
  calc ‖(g u : ℂ)‖ * u ^ k * ‖cexp (-z * u)‖
      ≤ C * Real.exp (2 * u) * u ^ k * Real.exp (-(2 + b) * u) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h3 (norm_nonneg _)
          (mul_nonneg hC (by positivity))
    _ = C * (u ^ k * (Real.exp (2 * u) * Real.exp (-(2 + b) * u))) := by ring
    _ = C * (u ^ k * Real.exp (-b * u)) := by
        rw [← Real.exp_add]
        ring_nf
end Deduction
