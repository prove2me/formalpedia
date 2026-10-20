-- Prove2me | solution 2 for CohnElkies.stripPoissonWeightedMeasure_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:31:14.032213+00:00
-- url     : https://prove2.me/submissions/cbfd446e-0075-45e7-abd4-1031ccb9ad9a

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology


theorem solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (f : ℝ → ℝ) (s : ℝ) :
    (∫ x : ℝ, f x ∂stripPoissonWeightedMeasure σ s) =
      ∫ x : ℝ, stripPoissonKernel σ (s - x) * f x := by
  have hθ0 : 0 < stripAngle σ := by unfold stripAngle; nlinarith [Real.pi_pos]
  have hθ1 : stripAngle σ < Real.pi := by unfold stripAngle; nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (stripAngle σ) := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ1
  have hcos : Real.cos (stripAngle σ) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ1.le hθ0
    simpa using this
  have hK : ∀ x, 0 ≤ stripPoissonKernel σ (s - x) := by
    intro x
    unfold stripPoissonKernel
    have := Real.one_le_cosh (Real.pi * (s - x) / 2)
    apply div_nonneg hsin.le
    linarith
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (stripPoissonKernel σ (s - x))) := by
    apply ENNReal.measurable_ofReal.comp
    unfold stripPoissonKernel
    fun_prop
  unfold stripPoissonWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmeas (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (hK x), smul_eq_mul]

