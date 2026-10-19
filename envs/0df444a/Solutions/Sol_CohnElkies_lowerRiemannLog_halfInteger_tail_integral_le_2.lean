-- Prove2me | solution 2 for CohnElkies.lowerRiemannLog_halfInteger_tail_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:21:24.439893+00:00
-- url     : https://prove2.me/submissions/2a7b9a78-f6f3-412d-a717-69839ef6aeef

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
    (k : ℕ) {ℓ T : ℝ}
    (hℓeq : ℓ = (k : ℝ) + 1 / 2)
    (hT : T ≠ 0) :
    ℓ * (∫ x in ((k : ℝ) / ℓ)..1,
      lowerRiemannLog T x) ≤
        (1 / 2 : ℝ) * lowerRiemannLog T 1 := by
  have hℓ : 0 < ℓ := by rw [hℓeq]; positivity
  have hT2 : 0 < T ^ 2 / 4 := by positivity
  have hk0 : 0 ≤ (k : ℝ) / ℓ := by positivity
  have hk1 : (k : ℝ) / ℓ ≤ 1 := by rw [div_le_one hℓ, hℓeq]; linarith
  have hcont : Continuous (fun x : ℝ => lowerRiemannLog T x) := by
    unfold lowerRiemannLog
    exact (Real.continuous_sqrt.comp (by fun_prop)).log
      (fun x => (Real.sqrt_pos.mpr (by positivity)).ne')
  have hle : ∀ x ∈ Set.Icc ((k : ℝ) / ℓ) 1, lowerRiemannLog T x ≤ lowerRiemannLog T 1 := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    unfold lowerRiemannLog
    apply Real.log_le_log (Real.sqrt_pos.mpr (by positivity))
    apply Real.sqrt_le_sqrt
    nlinarith
  calc ℓ * (∫ x in ((k : ℝ) / ℓ)..1, lowerRiemannLog T x)
      ≤ ℓ * ∫ x in ((k : ℝ) / ℓ)..1, lowerRiemannLog T 1 :=
        mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on hk1
          (hcont.intervalIntegrable _ _) intervalIntegrable_const hle) hℓ.le
    _ = ℓ * ((1 - (k : ℝ) / ℓ) * lowerRiemannLog T 1) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
    _ = (1 / 2 : ℝ) * lowerRiemannLog T 1 := by
        have : ℓ * (1 - (k : ℝ) / ℓ) = 1 / 2 := by
          field_simp; rw [hℓeq]; ring
        rw [← mul_assoc, this]

