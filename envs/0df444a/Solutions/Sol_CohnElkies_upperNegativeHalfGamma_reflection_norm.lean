-- Prove2me | solution 1 for CohnElkies.upperNegativeHalfGamma_reflection_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/32b2d660-c698-4aeb-b196-d1389a9a99df

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_norm_gamma_half_add_imaginary_sq
import Theorems.Thm_CohnElkies_upperNegativeHalfGammaArgument_ne_zero
import Theorems.Thm_CohnElkies_upperNegativeHalfGammaArgument_succ_add_one

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    (N : ℕ) (s : ℝ) :
    ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ *
      ‖Complex.Gamma
        (((((N : ℝ) + 3 / 2) : ℝ) : ℂ) +
          Complex.I * (((s / 2 : ℝ) : ℂ)))‖ =
      Real.pi / Real.cosh (Real.pi * (s / 2)) := by
  induction N with
  | zero =>
      let z : ℂ := (1 / 2 : ℂ) +
        Complex.I * (((s / 2 : ℝ) : ℂ))
      have hz : z ≠ 0 := by
        intro hz0
        have h := congrArg Complex.re hz0
        norm_num [z] at h
      have hneg : -z ≠ 0 := neg_ne_zero.mpr hz
      have hargneg : upperNegativeHalfGammaArgument 0 s = -z := by
        simp [upperNegativeHalfGammaArgument, z]
        ring
      have hargpos :
          (((((0 : ℕ) : ℝ) + 3 / 2 : ℝ) : ℂ) +
            Complex.I * (((s / 2 : ℝ) : ℂ))) = z + 1 := by
        simp [z]
        ring
      have hconjarg : -z + 1 = starRingEnd ℂ z := by
        try dsimp [z]
        simp only [map_add, map_div₀, Complex.conj_ofReal,
          Complex.conj_I, Complex.conj_ofNat, map_mul, map_one]
        push_cast
        ring
      have hnegRec := Complex.Gamma_add_one (-z) hneg
      rw [hconjarg, Complex.Gamma_conj] at hnegRec
      have hnegNorm :
          ‖Complex.Gamma z‖ =
            ‖z‖ * ‖Complex.Gamma (-z)‖ := by
        have h := congrArg norm hnegRec
        simpa [norm_mul] using! h
      have hposRec := Complex.Gamma_add_one z hz
      have hposNorm :
          ‖Complex.Gamma (z + 1)‖ =
            ‖z‖ * ‖Complex.Gamma z‖ := by
        simpa [norm_mul] using! congrArg norm hposRec
      rw [hargneg, hargpos, hposNorm]
      calc
        ‖Complex.Gamma (-z)‖ *
            (‖z‖ * ‖Complex.Gamma z‖) =
          (‖z‖ * ‖Complex.Gamma (-z)‖) *
            ‖Complex.Gamma z‖ := by ring
        _ = ‖Complex.Gamma z‖ ^ 2 := by
          rw [← hnegNorm]
          ring
        _ = Real.pi / Real.cosh (Real.pi * (s / 2)) := by
          try dsimp [z]
          convert! norm_gamma_half_add_imaginary_sq (s / 2)
            using 1
  | succ N ih =>
      let z : ℂ :=
        (((((N : ℝ) + 3 / 2) : ℝ) : ℂ) +
          Complex.I * (((s / 2 : ℝ) : ℂ)))
      have hz : z ≠ 0 := by
        intro hz0
        have h := congrArg Complex.re hz0
        simp [z] at h
        have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith
      have harg :
          upperNegativeHalfGammaArgument (N + 1) s = -z := by
        unfold upperNegativeHalfGammaArgument
        simp [z, Nat.cast_add, Nat.cast_one]
        ring
      have hpos :
          (((((N + 1 : ℕ) : ℝ) + 3 / 2 : ℝ) : ℂ) +
            Complex.I * (((s / 2 : ℝ) : ℂ))) = z + 1 := by
        simp [z, Nat.cast_add, Nat.cast_one]
        ring
      have hnegRec := Complex.Gamma_add_one
        (upperNegativeHalfGammaArgument (N + 1) s)
        (upperNegativeHalfGammaArgument_ne_zero (N + 1) s)
      rw [upperNegativeHalfGammaArgument_succ_add_one] at hnegRec
      have hnegNorm :
          ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ =
            ‖z‖ *
              ‖Complex.Gamma
                (upperNegativeHalfGammaArgument (N + 1) s)‖ := by
        have h := congrArg norm hnegRec
        rw [norm_mul, harg, norm_neg] at h
        simpa only [harg] using! h
      have hposRec := Complex.Gamma_add_one z hz
      have hposNorm :
          ‖Complex.Gamma (z + 1)‖ =
            ‖z‖ * ‖Complex.Gamma z‖ := by
        simpa [norm_mul] using! congrArg norm hposRec
      rw [hpos, hposNorm]
      calc
        ‖Complex.Gamma
            (upperNegativeHalfGammaArgument (N + 1) s)‖ *
            (‖z‖ * ‖Complex.Gamma z‖) =
          (‖z‖ *
            ‖Complex.Gamma
              (upperNegativeHalfGammaArgument (N + 1) s)‖) *
              ‖Complex.Gamma z‖ := by ring
        _ = ‖Complex.Gamma
            (upperNegativeHalfGammaArgument N s)‖ *
              ‖Complex.Gamma z‖ := by rw [← hnegNorm]
        _ = Real.pi / Real.cosh (Real.pi * (s / 2)) := by
          simpa [z] using! ih
end CohnElkies
