-- Prove2me | solution 1 for CohnElkies.normalizedRadialMellinStrip_bottom_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/f60ef09c-0ead-486a-aa5b-4e580f8e937c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialL1Mass_pos

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
    (hd : 0 < d) (f : TestFunction d) (hnonzero : f ≠ 0)
    (R : ℝ) (y : ℝ) :
    ‖normalizedRadialMellinStrip hd f R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ =
      (radialSurfaceArea d / radialL1Mass f) *
        Real.exp ((d : ℝ) * Real.log R) *
        ‖mellin (radialProfile hd f)
          (-(Complex.I * (y : ℂ)))‖ := by
  let z : ℂ :=
    (y : ℂ) - Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ)
  have hmass : 0 < radialL1Mass f :=
    radialL1Mass_pos f hnonzero
  have hsurface : 0 < radialSurfaceArea d :=
    radialSurfaceArea_pos hd
  have hmellin :
      (d : ℂ) / 2 - Complex.I * z =
        -(Complex.I * (y : ℂ)) := by
    try dsimp [z]
    push_cast
    simp [mul_sub, ← mul_assoc, Complex.I_mul_I]
  have hphase :
      ((((d : ℂ) / 2 + Complex.I * z) *
        (Real.log R : ℂ))).re =
          (d : ℝ) * Real.log R := by
    try dsimp [z]
    push_cast
    norm_num
  change ‖normalizedRadialMellinStrip hd f R z‖ = _
  unfold normalizedRadialMellinStrip radialMellinStrip
  rw [norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (div_pos hsurface hmass),
    Complex.norm_exp, hphase, hmellin]
end CohnElkies
