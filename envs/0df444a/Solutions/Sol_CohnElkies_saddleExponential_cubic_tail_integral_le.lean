-- Prove2me | solution 1 for CohnElkies.saddleExponential_cubic_tail_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/9ccace86-0c6a-44c8-bd75-9394ad6d50d1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integrable_exp_neg_mul_abs
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_le_two_exp_three_abs
import Theorems.Thm_CohnElkies_saddle_integral_exp_neg_mul_abs
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_mul_exp_abs_integrable
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
        Real.exp (-k * |T|)) ≤
      2 * Real.exp (-(k / 4) * R) *
        (2 / (k / 4)) := by
  have hkpos : 0 < k := by linarith
  have hquarter : 0 < k / 4 := by positivity
  let c : ℝ := 2 * Real.exp (-(k / 4) * R)
  have hc : 0 ≤ c := by
    try dsimp [c]
    positivity
  have hsource :=
    saddleGaussianTailWeight_mul_exp_abs_integrable hkpos
  have habs := integrable_exp_neg_mul_abs hquarter
  have hmajor : Integrable
      (fun T : ℝ => c * Real.exp (-(k / 4) * |T|)) :=
    habs.const_mul c
  have hpoint : ∀ T ∈ saddleGaussianTailSet R,
      saddleGaussianTailWeight T * Real.exp (-k * |T|) ≤
        c * Real.exp (-(k / 4) * |T|) := by
    intro T hT
    change R ≤ |T| at hT
    have hTabs : 0 ≤ |T| := hR.trans hT
    have hexponent :
        3 * |T| + (-k * |T|) ≤
          (-(k / 4) * R) + (-(k / 4) * |T|) := by
      nlinarith [
        mul_nonneg (show 0 ≤ k - 6 by linarith)
          hTabs,
        mul_nonneg (show 0 ≤ k by linarith)
          (show 0 ≤ |T| - R by linarith)]
    calc
      saddleGaussianTailWeight T * Real.exp (-k * |T|) ≤
          (2 * Real.exp (3 * |T|)) *
            Real.exp (-k * |T|) := by
              gcongr
              exact saddleGaussianTailWeight_le_two_exp_three_abs T
      _ = 2 * Real.exp
          (3 * |T| + (-k * |T|)) := by
            rw [Real.exp_add]
            ring
      _ ≤ 2 * Real.exp
          (-(k / 4) * R + (-(k / 4) * |T|)) := by
              gcongr
      _ = c * Real.exp (-(k / 4) * |T|) := by
            try dsimp [c]
            rw [Real.exp_add]
            ring
  have hcompare := setIntegral_mono_on
    hsource.integrableOn hmajor.integrableOn
    (saddleGaussianTailSet_measurable R) hpoint
  have hnonnegative :
      0 ≤ᵐ[(volume : Measure ℝ)]
        (fun T : ℝ => c * Real.exp (-(k / 4) * |T|)) :=
    Filter.Eventually.of_forall fun T =>
      mul_nonneg hc (Real.exp_pos _).le
  calc
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp (-k * |T|)) ≤
      ∫ T : ℝ in saddleGaussianTailSet R,
        c * Real.exp (-(k / 4) * |T|) := hcompare
    _ ≤ ∫ T : ℝ,
        c * Real.exp (-(k / 4) * |T|) :=
      setIntegral_le_integral hmajor hnonnegative
    _ = 2 * Real.exp (-(k / 4) * R) *
        (2 / (k / 4)) := by
      rw [integral_const_mul,
        saddle_integral_exp_neg_mul_abs hquarter]
end CohnElkies
