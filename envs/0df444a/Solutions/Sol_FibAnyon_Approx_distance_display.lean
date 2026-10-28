-- Prove2me | solution 1 for FibAnyon.Approx.distance_display
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:53:44.702398+00:00
-- url     : https://prove2.me/submissions/31092be1-5995-4faf-b04e-1968dfc9a533

import Mathlib
import Definitions.Def_FibAnyon_Approx_Model

noncomputable section

open FibAnyon.Approx in
theorem solution (φ : ℝ) (u v : ZOmega) (h : IsExact u v) :
    dist (Rz φ) (exactU u v 5) =
      Real.sqrt (1 - |(u.toC * Complex.exp (φ * Complex.I / 2)).re|) := by
  have hw5 : w10 ^ (5 : ℤ) = -1 := by
    rw [zpow_ofNat, w10, ← Complex.exp_nat_mul]
    have : ((5 : ℕ) : ℂ) * (Real.pi * Complex.I / 5) = Real.pi * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_pi_mul_I]
  set z := u.toC * Complex.exp (φ * Complex.I / 2) with hz
  have hconj : Complex.exp (-(φ * Complex.I) / 2) = star (Complex.exp (φ * Complex.I / 2)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    rw [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  have htr : Matrix.trace (Rz φ * (exactU u v 5).conjTranspose) = z + star z := by
    rw [Matrix.trace_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    simp [Rz, exactU, hw5]
    rw [hconj, hz]
    simp
    ring
  unfold FibAnyon.Approx.dist
  rw [htr]
  congr 2
  rw [Complex.star_def, Complex.add_conj, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  simp
