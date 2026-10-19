-- Prove2me | solution 1 for CohnElkies.radial_fourier_mellin_antifourier_boundary_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/33600f28-b706-48fd-853c-b9506c502510

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radial_fourier_mellin_antifourier_boundary

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
    ‖mellin (radialProfile hd f) (-(Complex.I * (y : ℂ)))‖ =
      Real.pi ^ ((d : ℝ) / 2) *
        (‖Complex.Gamma (-(Complex.I * (y : ℂ)) / 2)‖ /
          ‖Complex.Gamma
            (((d : ℝ) / 2 : ℝ) + Complex.I * (y : ℂ) / 2)‖) *
          ‖mellin (radialProfile hd f)
            ((d : ℂ) + Complex.I * (y : ℂ))‖ := by
  have hdenGamma :
      Complex.Gamma
        (((d : ℝ) / 2 : ℝ) + Complex.I * (y : ℂ) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num
    exact Nat.cast_pos.mpr hd
  have hden :
      ‖Complex.Gamma
        (((d : ℝ) / 2 : ℝ) + Complex.I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hdenGamma
  have hnorm := congrArg norm
    (radial_fourier_mellin_antifourier_boundary
      hd f hf hzero hanti y hy)
  simp only [norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos] at hnorm
  norm_num at hnorm
  calc
    ‖mellin (radialProfile hd f) (-(Complex.I * (y : ℂ)))‖ =
        (Real.pi ^ ((d : ℝ) / 2) *
          ‖Complex.Gamma (-(Complex.I * (y : ℂ)) / 2)‖ *
          ‖mellin (radialProfile hd f)
            ((d : ℂ) + Complex.I * (y : ℂ))‖) /
          ‖Complex.Gamma
            (((d : ℝ) / 2 : ℝ) + Complex.I * (y : ℂ) / 2)‖ := by
      apply (eq_div_iff hden).2
      push_cast
      convert! hnorm using 1; ring
    _ = Real.pi ^ ((d : ℝ) / 2) *
        (‖Complex.Gamma (-(Complex.I * (y : ℂ)) / 2)‖ /
          ‖Complex.Gamma
            (((d : ℝ) / 2 : ℝ) + Complex.I * (y : ℂ) / 2)‖) *
          ‖mellin (radialProfile hd f)
            ((d : ℂ) + Complex.I * (y : ℂ))‖ := by
      ring
end CohnElkies
