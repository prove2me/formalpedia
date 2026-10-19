-- Prove2me | solution 1 for CohnElkies.normalizedRadialMellinStrip_top_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/664cf3ed-daf4-440a-9de7-c1b578d36452

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialL1Mass_pos
import Theorems.Thm_CohnElkies_norm_schwartz_imaginaryRiesz_integral_le_L1

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
    (hd : 0 < d) (f : TestFunction d)
    (hf : IsRadial f) (hnonzero : f ≠ 0)
    (R : ℝ) (y : ℝ) :
    ‖normalizedRadialMellinStrip hd f R
        ((y : ℂ) +
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤ 1 := by
  let z : ℂ :=
    (y : ℂ) + Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ)
  let s : ℂ := (d : ℂ) - Complex.I * (y : ℂ)
  have hmass : 0 < radialL1Mass f :=
    radialL1Mass_pos f hnonzero
  have hsurface : 0 < radialSurfaceArea d :=
    radialSurfaceArea_pos hd
  have hmellin :
      (d : ℂ) / 2 - Complex.I * z = s := by
    try dsimp [z, s]
    push_cast
    simp [mul_add, ← mul_assoc, Complex.I_mul_I]; ring
  have hphase :
      ((((d : ℂ) / 2 + Complex.I * z) *
        (Real.log R : ℂ))).re = 0 := by
    try dsimp [z]
    push_cast
    norm_num
  have hpolar :
      (∫ x : Euclidean d,
        f x * (‖x‖ : ℂ) ^ (-(Complex.I * (y : ℂ)))) =
        radialSurfaceArea d • mellin (radialProfile hd f) s := by
    have hexponent : s - (d : ℂ) =
        -(Complex.I * (y : ℂ)) := by
      try dsimp [s]
      ring
    simpa only [hexponent] using!
      integral_radialProfile_cpow hd f hf s
  have hbound :
      radialSurfaceArea d * ‖mellin (radialProfile hd f) s‖ ≤
        radialL1Mass f := by
    calc
      radialSurfaceArea d * ‖mellin (radialProfile hd f) s‖ =
          ‖radialSurfaceArea d •
            mellin (radialProfile hd f) s‖ := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos hsurface]
      _ = ‖∫ x : Euclidean d,
          f x * (‖x‖ : ℂ) ^
            (-(Complex.I * (y : ℂ)))‖ := by
        rw [hpolar]
      _ ≤ radialL1Mass f :=
        norm_schwartz_imaginaryRiesz_integral_le_L1 hd f y
  change ‖normalizedRadialMellinStrip hd f R z‖ ≤ 1
  calc
    ‖normalizedRadialMellinStrip hd f R z‖ =
        (radialSurfaceArea d / radialL1Mass f) *
          ‖mellin (radialProfile hd f) s‖ := by
      unfold normalizedRadialMellinStrip radialMellinStrip
      rw [norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_pos (div_pos hsurface hmass),
        Complex.norm_exp, hphase, Real.exp_zero,
        hmellin]
      ring
    _ = (radialSurfaceArea d *
          ‖mellin (radialProfile hd f) s‖) /
            radialL1Mass f := by
      ring
    _ ≤ 1 := (div_le_one hmass).mpr hbound
end CohnElkies
