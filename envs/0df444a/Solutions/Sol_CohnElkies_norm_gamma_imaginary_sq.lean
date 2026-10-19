-- Prove2me | solution 1 for CohnElkies.norm_gamma_imaginary_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/36b72af9-80fd-4786-9a5f-fe01125f0a36

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
theorem _root_.solution {x : ℝ} (hx : x ≠ 0) :
    ‖Complex.Gamma (Complex.I * (x : ℂ))‖ ^ 2 =
      Real.pi / (x * Real.sinh (Real.pi * x)) := by
  let z : ℂ := Complex.I * (x : ℂ)
  have hz : -z ≠ 0 := by
    try dsimp [z]
    exact neg_ne_zero.mpr
      (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hx))
  have hrec :
      Complex.Gamma (1 - z) = (-z) * Complex.Gamma (-z) := by
    convert! Complex.Gamma_add_one (-z) hz using 1; ring_nf
  have hconjarg : -z = starRingEnd ℂ z := by
    try dsimp [z]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hconj :
      Complex.Gamma (-z) =
        starRingEnd ℂ (Complex.Gamma z) := by
    rw [hconjarg, Complex.Gamma_conj]
  have hsin :
      Complex.sin ((Real.pi : ℂ) * z) =
        (Real.sinh (Real.pi * x) : ℂ) * Complex.I := by
    have hinput :
        (Real.pi : ℂ) * z =
          ((Real.pi * x : ℝ) : ℂ) * Complex.I := by
      try dsimp [z]
      push_cast
      ring
    rw [hinput, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  have hsinh : Real.sinh (Real.pi * x) ≠ 0 :=
    Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hx)
  have hden : (Real.sinh (Real.pi * x) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hsinh) Complex.I_ne_zero
  have hprod :
      Complex.Gamma z * starRingEnd ℂ (Complex.Gamma z) =
        (‖Complex.Gamma z‖ ^ 2 : ℝ) := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have href := Complex.Gamma_mul_Gamma_one_sub z
  rw [hrec, hconj, hsin] at href
  have hidentity :
      ((‖Complex.Gamma z‖ ^ 2 *
        (x * Real.sinh (Real.pi * x)) : ℝ) : ℂ) =
          (Real.pi : ℂ) := by
    calc
      ((‖Complex.Gamma z‖ ^ 2 *
        (x * Real.sinh (Real.pi * x)) : ℝ) : ℂ) =
          (Complex.Gamma z * starRingEnd ℂ (Complex.Gamma z)) *
            ((x * Real.sinh (Real.pi * x) : ℝ) : ℂ) := by
        rw [hprod]
        push_cast
        rfl
      _ =
          (Complex.Gamma z *
            (-z * starRingEnd ℂ (Complex.Gamma z))) *
              ((Real.sinh (Real.pi * x) : ℂ) * Complex.I) := by
        try dsimp [z]
        rw [Complex.ofReal_mul]
        ring_nf
        simp [Complex.I_sq]
      _ = ((Real.pi : ℂ) /
          ((Real.sinh (Real.pi * x) : ℂ) * Complex.I)) *
            ((Real.sinh (Real.pi * x) : ℂ) * Complex.I) := by
        rw [href]
      _ = (Real.pi : ℂ) := div_mul_cancel₀ _ hden
  have hmul :
      ‖Complex.Gamma z‖ ^ 2 *
        (x * Real.sinh (Real.pi * x)) = Real.pi := by
    exact_mod_cast hidentity
  exact (eq_div_iff (mul_ne_zero hx hsinh)).2 hmul
end CohnElkies
