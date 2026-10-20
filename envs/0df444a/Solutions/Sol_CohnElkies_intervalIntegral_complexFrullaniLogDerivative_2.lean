-- Prove2me | solution 2 for CohnElkies.intervalIntegral_complexFrullaniLogDerivative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:31:20.559586+00:00
-- url     : https://prove2.me/submissions/3d34309e-5b39-4252-9550-b954920ed253

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    (∫ s in (0 : ℝ)..1,
      (w - z) * (complexFrullaniSegment z w s)⁻¹) =
      Complex.log w - Complex.log z := by
  have hre : ∀ s ∈ Set.uIcc (0:ℝ) 1, 0 < (complexFrullaniSegment z w s).re := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    unfold complexFrullaniSegment
    simp
    rcases le_total s (1/2) with h | h
    · nlinarith [mul_nonneg hs.1 hw.le, mul_nonneg (by linarith : (0:ℝ) ≤ 1/2 - s) hz.le]
    · nlinarith [mul_nonneg (by linarith [hs.2] : (0:ℝ) ≤ 1 - s) hz.le, mul_nonneg (by linarith : (0:ℝ) ≤ s - 1/2) hw.le]
  have hne : ∀ s ∈ Set.uIcc (0:ℝ) 1, complexFrullaniSegment z w s ≠ 0 := fun s hs h => by
    have := hre s hs; rw [h] at this; simp at this
  have hd : ∀ s ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun s : ℝ => Complex.log (complexFrullaniSegment z w s))
      ((w - z) * (complexFrullaniSegment z w s)⁻¹) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => complexFrullaniSegment z w s) (w - z) s := by
      unfold complexFrullaniSegment
      have := (((hasDerivAt_id s).ofReal_comp).mul_const (w - z)).const_add z
      simpa using this
    have := h1.clog_real (Or.inl (hre s hs))
    convert this using 1
    rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp [complexFrullaniSegment]
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ _ hne
    unfold complexFrullaniSegment
    fun_prop

