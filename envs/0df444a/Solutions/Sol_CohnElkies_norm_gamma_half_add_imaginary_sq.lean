-- Prove2me | solution 1 for CohnElkies.norm_gamma_half_add_imaginary_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/3d48dcf7-a663-4d80-8028-f461bf4c771e

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
namespace CohnElkies
theorem _root_.solution (x : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * x) := by
  let z : ℂ := (1 / 2 : ℂ) + Complex.I * (x : ℂ)
  have harg : 1 - z = starRingEnd ℂ z := by
    try dsimp [z]
    simp only [map_add, map_div₀, Complex.conj_ofReal,
      Complex.conj_I, Complex.conj_ofNat, map_mul, map_one]
    ring
  have hsin :
      Complex.sin ((Real.pi : ℂ) * z) =
        (Real.cosh (Real.pi * x) : ℂ) := by
    have hinput :
        (Real.pi : ℂ) * z =
          (Real.pi / 2 : ℝ) + (Real.pi * x : ℝ) * Complex.I := by
      try dsimp [z]
      push_cast
      ring
    have hsinhalf :
        Complex.sin ((Real.pi / 2 : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_sin, Real.sin_pi_div_two]
      norm_num
    have hcoshalf :
        Complex.cos ((Real.pi / 2 : ℝ) : ℂ) = 0 := by
      rw [← Complex.ofReal_cos, Real.cos_pi_div_two]
      norm_num
    rw [hinput, Complex.sin_add_mul_I, hsinhalf, hcoshalf]
    simp only [one_mul, zero_mul, add_zero]
    exact (Complex.ofReal_cosh (Real.pi * x)).symm
  have href := Complex.Gamma_mul_Gamma_one_sub z
  rw [harg, Complex.Gamma_conj, hsin] at href
  have hnorm :
      Complex.Gamma z * starRingEnd ℂ (Complex.Gamma z) =
        (‖Complex.Gamma z‖ ^ 2 : ℝ) := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  rw [hnorm] at href
  have hre := congrArg Complex.re href
  change
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ ^ 2 =
      (((Real.pi : ℝ) : ℂ) /
        (Real.cosh (Real.pi * x) : ℂ)).re at hre
  simpa only [Complex.div_ofReal_re] using! hre
end CohnElkies
