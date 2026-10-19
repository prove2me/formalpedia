-- Prove2me | solution 2 for CohnElkies.intervalIntegral_complexLaplaceSegment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:05:35.799091+00:00
-- url     : https://prove2.me/submissions/f0213578-bf28-4626-a5ab-14cf68a598ee

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
    (z w : ℂ) {x : ℝ} (hx : x ≠ 0) :
    (∫ s in (0 : ℝ)..1,
      (w - z) *
        Complex.exp
          (-complexFrullaniSegment z w s * (x : ℂ))) =
      complexFrullaniKernel z w x := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have h0 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := fun s => by
    simpa using (hasDerivAt_id s).ofReal_comp
  have hd : ∀ s : ℝ, HasDerivAt
      (fun s : ℝ => -Complex.exp (-complexFrullaniSegment z w s * (x : ℂ)) / (x : ℂ))
      ((w - z) * Complex.exp (-complexFrullaniSegment z w s * (x : ℂ))) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -complexFrullaniSegment z w s * (x : ℂ))
        (-(w - z) * x) s := by
      have := (((h0 s).mul_const (w - z)).const_add z).neg.mul_const (x : ℂ)
      unfold complexFrullaniSegment
      exact this.congr_deriv (by ring)
    have h2 := (h1.cexp.neg).div_const (x : ℂ)
    exact h2.congr_deriv (by rw [div_eq_iff hx']; ring)
  have hc : Continuous (fun s : ℝ => (w - z) * Complex.exp (-complexFrullaniSegment z w s * (x : ℂ))) := by
    unfold complexFrullaniSegment; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hc.intervalIntegrable _ _)]
  unfold complexFrullaniKernel complexFrullaniSegment
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero]
  rw [show z + (w - z) = w by ring]
  ring

