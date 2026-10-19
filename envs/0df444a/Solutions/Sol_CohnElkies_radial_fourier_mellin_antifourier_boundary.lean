-- Prove2me | solution 1 for CohnElkies.radial_fourier_mellin_antifourier_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/ed52140e-22a2-4bd4-94da-fcc4ed32f4d1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radial_fourier_mellin_regularized_closed

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
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (hanti : (𝓕 f : TestFunction d) = -f)
    (y : ℝ) (hy : y ≠ 0) :
    Complex.Gamma
        (((d : ℝ) / 2 : ℝ) + Complex.I * (y : ℂ) / 2) *
        mellin (radialProfile hd f) (-(Complex.I * (y : ℂ))) =
      -((Real.pi : ℂ) ^
          (((d : ℂ) / 2) + Complex.I * (y : ℂ)) *
        Complex.Gamma (-(Complex.I * (y : ℂ)) / 2) *
        mellin (radialProfile hd f)
          ((d : ℂ) + Complex.I * (y : ℂ))) := by
  let s : ℂ := -(Complex.I * (y : ℂ))
  have hhatZero :
      (𝓕 f : TestFunction d) (0 : Euclidean d) = 0 := by
    rw [hanti]
    simpa using! congrArg Neg.neg hzero
  have hs : 0 ≤ s.re := by
    try dsimp [s]
    norm_num
  have hsd : s.re ≤ (d : ℝ) := by
    try dsimp [s]
    norm_num
  have hnum : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have him := congrArg Complex.im hn
    try dsimp [s] at him
    norm_num at him
    apply hy
    linarith
  have hden : Complex.Gamma (((d : ℂ) - s) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    try dsimp [s]
    norm_num
    exact Nat.cast_pos.mpr hd
  have heq := radial_fourier_mellin_regularized_closed
    hd f hf hzero hhatZero s hs hsd
  have hprofile :
      mellin (radialProfile hd (𝓕 f : TestFunction d)) s =
        -(mellin (radialProfile hd f) s) := by
    rw [hanti]
    simp [radialProfile, mellin, integral_neg]
  rw [hprofile] at heq
  have hcross :
      Complex.Gamma (((d : ℂ) - s) / 2) *
          mellin (radialProfile hd f) s =
        -((Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
          Complex.Gamma (s / 2) *
          mellin (radialProfile hd f) ((d : ℂ) - s)) := by
    field_simp [hnum, hden] at heq ⊢
    linear_combination -heq
  convert! hcross using 1 <;> dsimp [s] <;>
    push_cast <;> ring_nf
end CohnElkies
