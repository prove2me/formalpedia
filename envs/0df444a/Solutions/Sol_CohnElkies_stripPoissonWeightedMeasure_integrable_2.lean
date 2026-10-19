-- Prove2me | solution 2 for CohnElkies.stripPoissonWeightedMeasure_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:24:50.354133+00:00
-- url     : https://prove2.me/submissions/bffbc2d5-03c2-479a-8471-ecc7efaae3f4

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
    {f : ℝ → ℝ} (hf : Integrable f) (s : ℝ) :
    Integrable f (stripPoissonWeightedMeasure σ s) := by
  set θ := stripAngle σ with hθ
  have hθ0 : 0 < θ := by rw [hθ]; unfold stripAngle; have := Real.pi_pos; nlinarith
  have hθπ : θ < Real.pi := by rw [hθ]; unfold stripAngle; have := Real.pi_pos; nlinarith
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hcos : Real.cos θ < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ.le hθ0
    simpa using this
  set C := Real.sin θ / (4 * (1 - Real.cos θ)) with hC
  have hbound : ∀ x, stripPoissonKernel σ (s - x) ≤ C := by
    intro x
    unfold stripPoissonKernel
    rw [← hθ]
    have h1 := Real.one_le_cosh (Real.pi * (s - x) / 2)
    exact div_le_div_of_nonneg_left hsin.le (by nlinarith) (by nlinarith)
  have hle : stripPoissonWeightedMeasure σ s ≤ (ENNReal.ofReal C) • (volume : Measure ℝ) := by
    unfold stripPoissonWeightedMeasure
    rw [← withDensity_const]
    exact withDensity_mono (Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hbound x))
  exact (hf.smul_measure ENNReal.ofReal_ne_top).mono_measure hle

