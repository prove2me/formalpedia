-- Prove2me | solution 1 for CohnElkies.saddleGaussian_cubic_tail_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/0d7d2f48-09df-4863-955c-f8965296c6d6

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_le_two_exp_three_sq
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_mul_gaussian_integrable
import Theorems.Thm_CohnElkies_saddleGaussianTailSet_measurable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {k R : ℝ} (hk : 6 ≤ k) (hR : 0 ≤ R) :
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp (-k * T ^ 2)) ≤
      2 * Real.exp (-(k / 4) * R ^ 2) *
        Real.sqrt (Real.pi / (k / 4)) := by
  have hkpos : 0 < k := by linarith
  have hquarter : 0 < k / 4 := by positivity
  let c : ℝ := 2 * Real.exp (-(k / 4) * R ^ 2)
  have hc : 0 ≤ c := by
    try dsimp [c]
    positivity
  have hsource :=
    saddleGaussianTailWeight_mul_gaussian_integrable hkpos
  have hgaussian := integrable_exp_neg_mul_sq hquarter
  have hmajor : Integrable
      (fun T : ℝ => c * Real.exp (-(k / 4) * T ^ 2)) :=
    hgaussian.const_mul c
  have hpoint : ∀ T ∈ saddleGaussianTailSet R,
      saddleGaussianTailWeight T * Real.exp (-k * T ^ 2) ≤
        c * Real.exp (-(k / 4) * T ^ 2) := by
    intro T hT
    change R ≤ |T| at hT
    have hsq : R ^ 2 ≤ T ^ 2 := by
      have h := pow_le_pow_left₀ hR hT 2
      simpa [sq_abs] using! h
    have hexponent :
        3 * T ^ 2 + (-k * T ^ 2) ≤
          (-(k / 4) * R ^ 2) +
            (-(k / 4) * T ^ 2) := by
      nlinarith [
        mul_nonneg (show 0 ≤ k - 6 by linarith)
          (sq_nonneg T),
        mul_nonneg (show 0 ≤ k by linarith)
          (show 0 ≤ T ^ 2 - R ^ 2 by linarith)]
    calc
      saddleGaussianTailWeight T * Real.exp (-k * T ^ 2) ≤
          (2 * Real.exp (3 * T ^ 2)) *
            Real.exp (-k * T ^ 2) := by
              gcongr
              exact saddleGaussianTailWeight_le_two_exp_three_sq T
      _ = 2 * Real.exp
          (3 * T ^ 2 + (-k * T ^ 2)) := by
            rw [Real.exp_add]
            ring
      _ ≤ 2 * Real.exp
          (-(k / 4) * R ^ 2 +
            (-(k / 4) * T ^ 2)) := by
              gcongr
      _ = c * Real.exp (-(k / 4) * T ^ 2) := by
            try dsimp [c]
            rw [Real.exp_add]
            ring
  have hcompare := setIntegral_mono_on
    hsource.integrableOn hmajor.integrableOn
    (saddleGaussianTailSet_measurable R) hpoint
  have hnonnegative :
      0 ≤ᵐ[(volume : Measure ℝ)]
        (fun T : ℝ => c * Real.exp (-(k / 4) * T ^ 2)) :=
    Filter.Eventually.of_forall fun T =>
      mul_nonneg hc (Real.exp_pos _).le
  calc
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp (-k * T ^ 2)) ≤
      ∫ T : ℝ in saddleGaussianTailSet R,
        c * Real.exp (-(k / 4) * T ^ 2) := hcompare
    _ ≤ ∫ T : ℝ,
        c * Real.exp (-(k / 4) * T ^ 2) :=
      setIntegral_le_integral hmajor hnonnegative
    _ = 2 * Real.exp (-(k / 4) * R ^ 2) *
        Real.sqrt (Real.pi / (k / 4)) := by
      rw [integral_const_mul, integral_gaussian]
end CohnElkies
