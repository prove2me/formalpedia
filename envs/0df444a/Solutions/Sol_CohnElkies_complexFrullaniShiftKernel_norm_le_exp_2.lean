-- Prove2me | solution 2 for CohnElkies.complexFrullaniShiftKernel_norm_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:07:18.590476+00:00
-- url     : https://prove2.me/submissions/2110d134-9413-43c0-9670-462d424b1cd5

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
theorem h47_laplace (z w : ℂ) {x : ℝ} (hx : x ≠ 0) :
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

theorem h47_frullani_bound (z w : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖complexFrullaniKernel z w x‖ ≤ ‖w - z‖ * Real.exp (-(min z.re w.re) * x) := by
  rw [← h47_laplace z w hx.ne']
  have key : ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖(w - z) * Complex.exp (-complexFrullaniSegment z w t * (x : ℂ))‖ ≤
        ‖w - z‖ * Real.exp (-(min z.re w.re) * x) := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    rw [norm_mul, Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.2
    have hre : (-complexFrullaniSegment z w t * (x : ℂ)).re = -(z.re + t * (w.re - z.re)) * x := by
      unfold complexFrullaniSegment; simp; try ring
    rw [hre]
    have hm : min z.re w.re ≤ z.re + t * (w.re - z.re) := by
      rcases le_total z.re w.re with h | h
      · rw [min_eq_left h]; nlinarith [ht.1]
      · rw [min_eq_right h]; nlinarith [ht.2]
    nlinarith
  have := intervalIntegral.norm_integral_le_of_norm_le_const key
  simpa using this

theorem solution
    (z : ℂ) {s x : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hx : 0 < x) :
    ‖complexFrullaniKernel (z + (s : ℂ)) 1 x‖ ≤
      (‖(1 : ℂ) - z‖ + 1) *
        Real.exp (-(min z.re 1) * x) := by
  have hb := h47_frullani_bound (z + (s : ℂ)) 1 hx
  have h1 : ‖(1 : ℂ) - (z + (s : ℂ))‖ ≤ ‖(1 : ℂ) - z‖ + 1 := by
    calc ‖(1 : ℂ) - (z + (s : ℂ))‖ = ‖((1 : ℂ) - z) - (s : ℂ)‖ := by congr 1; ring
      _ ≤ ‖(1 : ℂ) - z‖ + ‖(s : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖(1 : ℂ) - z‖ + 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2]
  have h2 : Real.exp (-(min (z + (s : ℂ)).re (1 : ℂ).re) * x) ≤ Real.exp (-(min z.re 1) * x) := by
    apply Real.exp_le_exp.2
    have : min z.re 1 ≤ min (z + (s : ℂ)).re (1 : ℂ).re := by
      rw [Complex.add_re, Complex.ofReal_re, Complex.one_re]
      exact min_le_min (by linarith [hs.1]) le_rfl
    nlinarith
  calc ‖complexFrullaniKernel (z + (s : ℂ)) 1 x‖
      ≤ ‖(1 : ℂ) - (z + (s : ℂ))‖ * Real.exp (-(min (z + (s : ℂ)).re (1 : ℂ).re) * x) := hb
    _ ≤ (‖(1 : ℂ) - z‖ + 1) * Real.exp (-(min z.re 1) * x) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

