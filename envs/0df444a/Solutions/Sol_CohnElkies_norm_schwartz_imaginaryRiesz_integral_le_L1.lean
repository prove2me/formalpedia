-- Prove2me | solution 1 for CohnElkies.norm_schwartz_imaginaryRiesz_integral_le_L1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/a878d4d8-ad7d-419f-8bd9-a230b780694b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_norm_nonnegative_imaginary_cpow_le_one
import Theorems.Thm_CohnElkies_schwartz_imaginaryRiesz_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (t : ℝ) :
    ‖∫ x : Euclidean d,
      f x * (‖x‖ : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
      radialL1Mass f := by
  calc
    ‖∫ x : Euclidean d,
      f x * (‖x‖ : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
        ∫ x : Euclidean d,
          ‖f x * (‖x‖ : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : Euclidean d, ‖f x‖ := by
      apply integral_mono
        (schwartz_imaginaryRiesz_integrable hd f t).norm
        f.integrable.norm
      intro x
      try dsimp
      rw [norm_mul]
      calc
        ‖f x‖ *
            ‖(‖x‖ : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
          ‖f x‖ * 1 :=
            mul_le_mul_of_nonneg_left
              (norm_nonnegative_imaginary_cpow_le_one
                ‖x‖ t (norm_nonneg x))
              (norm_nonneg _)
        _ = ‖f x‖ := mul_one _
    _ = radialL1Mass f := rfl
end CohnElkies
