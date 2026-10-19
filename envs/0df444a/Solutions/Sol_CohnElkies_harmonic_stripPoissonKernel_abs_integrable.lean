-- Prove2me | solution 1 for CohnElkies.harmonic_stripPoissonKernel_abs_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/e13f1d34-60eb-47a9-9e4b-dbd1606e8a70

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_lower_product_integrable
import Theorems.Thm_CohnElkies_stripPoissonKernel_le_exponentialMajorant_of_nonneg
import Theorems.Thm_CohnElkies_harmonic_stripPoissonExponentialMajorant_abs_integrable
import Theorems.Thm_CohnElkies_harmonic_stripPoissonKernel_zero_abs_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable
      (fun T : ℝ => stripPoissonKernel σ T * |T|) := by
  by_cases hσ : σ ≤ 0
  · exact stripPoissonKernel_lower_product_integrable
      hbelow hσ continuous_abs
      harmonic_stripPoissonKernel_zero_abs_integrable
  · have hpositive : 0 ≤ σ := (le_of_not_ge hσ)
    have hmajor :=
      harmonic_stripPoissonExponentialMajorant_abs_integrable
    have hmeas : Measurable
        (fun T : ℝ => stripPoissonKernel σ T * |T|) := by
      unfold stripPoissonKernel stripAngle
      fun_prop
    apply hmajor.mono' hmeas.aestronglyMeasurable
    filter_upwards [] with T
    have hkernel :=
      stripPoissonKernel_le_exponentialMajorant_of_nonneg
        hpositive habove T
    have hkpos := stripPoissonKernel_pos
      hbelow habove T
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg hkpos.le (abs_nonneg T))]
    exact mul_le_mul_of_nonneg_right
      hkernel (abs_nonneg T)
end CohnElkies
