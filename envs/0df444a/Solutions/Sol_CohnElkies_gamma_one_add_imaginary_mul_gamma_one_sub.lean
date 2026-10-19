-- Prove2me | solution 1 for CohnElkies.gamma_one_add_imaginary_mul_gamma_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/1af32363-3cbe-4eaf-b523-814755b8b4b4

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_norm_gamma_imaginary_sq

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {x : ℝ} (hx : x ≠ 0) :
    Complex.Gamma (1 + Complex.I * (x : ℂ)) *
        Complex.Gamma (1 - Complex.I * (x : ℂ)) =
      ((Real.pi * x / Real.sinh (Real.pi * x) : ℝ) : ℂ) := by
  let z : ℂ := Complex.I * (x : ℂ)
  have hz : z ≠ 0 := by
    try dsimp [z]
    exact mul_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr hx)
  have hnegz : -z ≠ 0 := neg_ne_zero.mpr hz
  have hplus :
      Complex.Gamma (1 + z) = z * Complex.Gamma z := by
    convert! Complex.Gamma_add_one z hz using 1; ring_nf
  have hminus :
      Complex.Gamma (1 - z) =
        (-z) * Complex.Gamma (-z) := by
    convert! Complex.Gamma_add_one (-z) hnegz using 1; ring_nf
  have hconjarg : -z = starRingEnd ℂ z := by
    try dsimp [z]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hgammaprod :
      Complex.Gamma z * Complex.Gamma (-z) =
        (‖Complex.Gamma z‖ ^ 2 : ℝ) := by
    rw [hconjarg, Complex.Gamma_conj, mul_comm,
      ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have hsinh : Real.sinh (Real.pi * x) ≠ 0 :=
    Real.sinh_ne_zero.mpr
      (mul_ne_zero Real.pi_ne_zero hx)
  change Complex.Gamma (1 + z) *
    Complex.Gamma (1 - z) = _
  rw [hplus, hminus]
  calc
    (z * Complex.Gamma z) *
        ((-z) * Complex.Gamma (-z)) =
      ((x ^ 2 : ℝ) : ℂ) *
        (Complex.Gamma z * Complex.Gamma (-z)) := by
          try dsimp [z]
          ring_nf
          simp [Complex.I_sq]
          ring
    _ = ((x ^ 2 * ‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) := by
      rw [hgammaprod]
      push_cast
      ring
    _ = ((Real.pi * x / Real.sinh (Real.pi * x) : ℝ) : ℂ) := by
      try dsimp [z]
      rw [norm_gamma_imaginary_sq hx]
      congr 1
      field_simp [hx, hsinh]
end CohnElkies
