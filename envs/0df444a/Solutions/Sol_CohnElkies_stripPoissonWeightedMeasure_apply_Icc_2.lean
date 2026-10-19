-- Prove2me | solution 2 for CohnElkies.stripPoissonWeightedMeasure_apply_Icc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:02:08.02773+00:00
-- url     : https://prove2.me/submissions/a3c2b244-2c3a-4a2e-8306-6e91c718902d

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
    (s a b : ℝ) :
    stripPoissonWeightedMeasure σ s (Icc a b) =
      ENNReal.ofReal
        (∫ x in Icc a b,
          stripPoissonKernel σ (s - x)) := by
  unfold stripPoissonWeightedMeasure
  rw [MeasureTheory.withDensity_apply _ measurableSet_Icc]
  have hp := Real.pi_pos
  have hθ0 : 0 < stripAngle σ := by unfold stripAngle; nlinarith
  have hθπ : stripAngle σ < Real.pi := by unfold stripAngle; nlinarith
  have hsin := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hcos : Real.cos (stripAngle σ) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ.le hθ0
    rwa [Real.cos_zero] at this
  have hden : ∀ x : ℝ, 0 < 4 * (Real.cosh (Real.pi * x / 2) - Real.cos (stripAngle σ)) := by
    intro x
    have := Real.one_le_cosh (Real.pi * x / 2)
    linarith
  have hcont : Continuous (fun x : ℝ => stripPoissonKernel σ (s - x)) := by
    unfold stripPoissonKernel
    exact Continuous.div continuous_const (by fun_prop) (fun x => (hden _).ne')
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc
    (MeasureTheory.ae_of_all _ (fun x => (div_pos hsin (hden _)).le))]

