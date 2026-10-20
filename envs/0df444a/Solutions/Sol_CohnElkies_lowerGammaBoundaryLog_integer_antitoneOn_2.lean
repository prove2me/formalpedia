-- Prove2me | solution 2 for CohnElkies.lowerGammaBoundaryLog_integer_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:57:51.400681+00:00
-- url     : https://prove2.me/submissions/cecef326-b9bd-4b27-8fc4-ad9068ec0003

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
theorem h47_gamma_shift_prod (z : ℂ) (hz : z.im ≠ 0) (k : ℕ) :
    Complex.Gamma (z + k) = Complex.Gamma z * ∏ j ∈ Finset.range k, (z + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hne : z + (k : ℂ) ≠ 0 := by
      intro h; apply hz; have := congrArg Complex.im h; simpa using this
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hne, ih, Finset.prod_range_succ]
    ring

theorem h47_int_formula (k : ℕ) (R : ℝ) {y : ℝ} (hy : 0 < y) :
    CohnElkies.lowerGammaBoundaryLog (k : ℝ) R y =
      (k : ℝ) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k, Real.log ‖Complex.I * (y : ℂ) / 2 + (j : ℂ)‖ := by
  unfold CohnElkies.lowerGammaBoundaryLog
  set z : ℂ := Complex.I * (y : ℂ) / 2 with hzdef
  have hzim : z.im = y / 2 := by rw [hzdef]; simp
  have hzim0 : z.im ≠ 0 := by rw [hzim]; positivity
  have hconj : -Complex.I * (y : ℂ) / 2 = starRingEnd ℂ z := by
    rw [hzdef]
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  have h1 : ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ = ‖Complex.Gamma z‖ := by
    rw [hconj, Complex.Gamma_conj, Complex.norm_conj]
  have h2 : (((k : ℝ) : ℂ) + Complex.I * (y : ℂ) / 2) = z + (k : ℂ) := by
    rw [hzdef]; push_cast; ring
  have hG : Complex.Gamma z ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm; apply hzim0; rw [hm]; simp
  have hP : ∀ j ∈ Finset.range k, z + (j : ℂ) ≠ 0 := by
    intro j _ h; apply hzim0; have := congrArg Complex.im h; simpa using this
  rw [h1, h2, h47_gamma_shift_prod z hzim0 k, norm_mul, Complex.norm_prod,
    Real.log_mul (norm_ne_zero_iff.mpr hG) (by
      rw [Finset.prod_ne_zero_iff]; intro j hj; exact norm_ne_zero_iff.mpr (hP j hj)),
    Real.log_prod (fun j hj => norm_ne_zero_iff.mpr (hP j hj))]
  ring

theorem solution
    (k : ℕ) (R : ℝ) :
    AntitoneOn (lowerGammaBoundaryLog (k : ℝ) R)
      (Ioi (0 : ℝ)) := by
  intro y1 hy1 y2 hy2 hle
  have hy1' : (0:ℝ) < y1 := hy1
  have hy2' : (0:ℝ) < y2 := hy2
  rw [h47_int_formula k R hy1', h47_int_formula k R hy2']
  have hmono : ∀ j ∈ Finset.range k, Real.log ‖Complex.I * (y1 : ℂ) / 2 + (j : ℂ)‖ ≤
      Real.log ‖Complex.I * (y2 : ℂ) / 2 + (j : ℂ)‖ := by
    intro j _
    have hpos : 0 < ‖Complex.I * (y1 : ℂ) / 2 + (j : ℂ)‖ := by
      apply norm_pos_iff.mpr
      intro h; have := congrArg Complex.im h; simp at this; linarith
    apply Real.log_le_log hpos
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
      Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp
    nlinarith
  linarith [Finset.sum_le_sum hmono]

