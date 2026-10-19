-- Prove2me | solution 2 for CohnElkies.lowerGammaBoundaryLog_halfInteger_factorized
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:05:44.708654+00:00
-- url     : https://prove2.me/submissions/e8ebc07b-4126-4715-842d-716793e600ab

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
theorem h47_gamma_shift (n : ℕ) (t : ℝ) :
    ‖Complex.Gamma ((((n : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ =
      ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (t : ℂ))‖ *
        ∏ j ∈ Finset.range n, Real.sqrt (((j : ℝ) + 1 / 2) ^ 2 + t ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : (((n : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      have : (0:ℝ) ≤ n := n.cast_nonneg
      linarith
    rw [show ((((n + 1 : ℕ) : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ) =
      ((((n : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ hs, norm_mul, ih, Finset.prod_range_succ]
    have hn : ‖(((n : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)‖ =
        Real.sqrt (((n : ℝ) + 1 / 2) ^ 2 + t ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]
      congr 1
      simp
      ring
    rw [hn]
    ring

theorem h47_norm_gamma_neg (y : ℝ) :
    ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ =
      ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ := by
  have h : -Complex.I * (y : ℂ) / 2 = (starRingEnd ℂ) (Complex.I * (y : ℂ) / 2) := by
    rw [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal,
      show (starRingEnd ℂ) 2 = 2 from map_ofNat _ 2]
    try ring
  rw [h, Complex.Gamma_conj, Complex.norm_conj]

theorem solution
    (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y =
      ((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
        (Real.log ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ -
          Real.log
            ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2)‖) := by
  unfold lowerGammaBoundaryLog
  have h2 : (((k : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ) / 2 =
      (((k : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ) := by push_cast; ring
  have h3 : (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2 = (1 / 2 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h47_norm_gamma_neg, h2, h47_gamma_shift, h3]
  have hpos : ∀ j ∈ Finset.range k, Real.sqrt (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2) ≠ 0 := by
    intro j _
    apply (Real.sqrt_pos.2 _).ne'
    have : (0:ℝ) < (j : ℝ) + 1 / 2 := by positivity
    nlinarith
  have hG : ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    apply Complex.Gamma_ne_zero
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := m.cast_nonneg
    linarith
  rw [Real.log_mul hG (Finset.prod_ne_zero_iff.2 hpos), Real.log_prod hpos]
  ring

