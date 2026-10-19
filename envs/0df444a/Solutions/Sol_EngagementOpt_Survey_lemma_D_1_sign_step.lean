-- Prove2me | solution 1 for EngagementOpt.Survey.lemma_D_1_sign_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T10:23:20.919994+00:00
-- url     : https://prove2.me/submissions/264cc032-7473-4872-ab0d-b3fc7efc4c0e

import Mathlib

set_option autoImplicit false

lemma D1_hasDeriv (x : ℝ) (hx : -1 < x) :
    HasDerivAt (fun t : ℝ => Real.log (t + 1) - 2 * t / (t + 2))
      (x ^ 2 / ((x + 1) * (x + 2) ^ 2)) x := by
  have h1 : x + 1 ≠ 0 := by intro h; linarith
  have h2 : x + 2 ≠ 0 := by intro h; linarith
  have hl : HasDerivAt (fun t : ℝ => Real.log (t + 1)) (1 / (x + 1)) x := by
    have := (((hasDerivAt_id' x).add_const 1).log h1)
    exact this.congr_deriv (by ring)
  have hq : HasDerivAt (fun t : ℝ => 2 * t / (t + 2)) ((2 * (x + 2) - 2 * x * 1) / (x + 2) ^ 2) x := by
    have := ((hasDerivAt_id' x).const_mul 2).div ((hasDerivAt_id' x).add_const 2) h2
    exact this.congr_deriv (by ring)
  refine (hl.sub hq).congr_deriv ?_
  field_simp
  ring

lemma D1_mono : MonotoneOn (fun t : ℝ => Real.log (t + 1) - 2 * t / (t + 2)) (Set.Ioi (-1)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi (-1))
  · intro x hx
    exact (D1_hasDeriv x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (D1_hasDeriv x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx' : (-1 : ℝ) < x := hx
    rw [(D1_hasDeriv x hx').deriv]
    have h1 : 0 < x + 1 := by linarith
    have h2 : 0 < x + 2 := by linarith
    positivity

theorem solution :
    (∀ x : ℝ, 0 < x → 0 ≤ (x + 2) * Real.log (x + 1) - 2 * x) ∧
    (∀ x : ℝ, -1 < x → x < 0 → (x + 2) * Real.log (x + 1) - 2 * x ≤ 0) := by
  have h0 : (fun t : ℝ => Real.log (t + 1) - 2 * t / (t + 2)) 0 = 0 := by simp
  constructor
  · intro x hx
    have := D1_mono (show (0:ℝ) ∈ Set.Ioi (-1) by simp) (show x ∈ Set.Ioi (-1) by
      simp only [Set.mem_Ioi]; linarith) hx.le
    rw [h0] at this
    simp only at this
    have h2 : 0 < x + 2 := by linarith
    have : 2 * x / (x + 2) ≤ Real.log (x + 1) := by linarith
    rw [div_le_iff₀ h2] at this
    linarith
  · intro x hx1 hx0
    have := D1_mono (show x ∈ Set.Ioi (-1) from hx1) (show (0:ℝ) ∈ Set.Ioi (-1) by simp) hx0.le
    rw [h0] at this
    simp only at this
    have h2 : 0 < x + 2 := by linarith
    have : Real.log (x + 1) ≤ 2 * x / (x + 2) := by linarith
    rw [le_div_iff₀ h2] at this
    linarith
