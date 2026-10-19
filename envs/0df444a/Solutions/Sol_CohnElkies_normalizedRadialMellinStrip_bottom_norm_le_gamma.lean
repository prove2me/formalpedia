-- Prove2me | solution 1 for CohnElkies.normalizedRadialMellinStrip_bottom_norm_le_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/c889ce10-3493-4dcb-9fb0-d61ac835f2eb

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedRadialMellinStrip_top_norm_le_one
import Theorems.Thm_CohnElkies_radial_fourier_mellin_antifourier_boundary_norm
import Theorems.Thm_CohnElkies_normalizedRadialMellinStrip_top_norm_eq
import Theorems.Thm_CohnElkies_normalizedRadialMellinStrip_bottom_norm_eq
import Theorems.Thm_CohnElkies_radialGammaBoundaryExponent_exp

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
    (hnonzero : f ≠ 0)
    (R : ℝ) (hR : 0 < R) (y : ℝ) (hy : y ≠ 0) :
    ‖normalizedRadialMellinStrip hd f R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤
      Real.exp
        (((d : ℝ) / 2) * Real.log (Real.pi * R ^ 2) +
          Real.log
            ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ -
          Real.log
            ‖Complex.Gamma
              (((d : ℝ) / 2 : ℝ) +
                Complex.I * (y : ℂ) / 2)‖) := by
  have hnumGamma :
      Complex.Gamma (-Complex.I * (y : ℂ) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have him := congrArg Complex.im hn
    norm_num at him
    apply hy
    linarith
  have hdenGamma :
      Complex.Gamma
        (((d : ℝ) / 2 : ℝ) +
          Complex.I * (y : ℂ) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num
    exact Nat.cast_pos.mpr hd
  have hnum :
      0 < ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ :=
    norm_pos_iff.mpr hnumGamma
  have hden :
      0 < ‖Complex.Gamma
        (((d : ℝ) / 2 : ℝ) +
          Complex.I * (y : ℂ) / 2)‖ :=
    norm_pos_iff.mpr hdenGamma
  have htop :=
    normalizedRadialMellinStrip_top_norm_le_one
      hd f hf hnonzero R (-y)
  rw [normalizedRadialMellinStrip_top_norm_eq
    hd f hnonzero R (-y)] at htop
  have hdual :
      (radialSurfaceArea d / radialL1Mass f) *
        ‖mellin (radialProfile hd f)
          ((d : ℂ) + Complex.I * (y : ℂ))‖ ≤ 1 := by
    simpa using! htop
  have hboundary :=
    radial_fourier_mellin_antifourier_boundary_norm
      hd f hf hzero hanti y hy
  have harg :
      -(Complex.I * (y : ℂ)) / 2 =
        -Complex.I * (y : ℂ) / 2 := by
    ring
  rw [harg] at hboundary
  have hfactor :
      0 ≤ Real.exp ((d : ℝ) * Real.log R) *
        Real.pi ^ ((d : ℝ) / 2) *
        (‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ /
          ‖Complex.Gamma
            (((d : ℝ) / 2 : ℝ) +
              Complex.I * (y : ℂ) / 2)‖) := by
    positivity
  calc
    ‖normalizedRadialMellinStrip hd f R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ =
        (radialSurfaceArea d / radialL1Mass f) *
          Real.exp ((d : ℝ) * Real.log R) *
          ‖mellin (radialProfile hd f)
            (-(Complex.I * (y : ℂ)))‖ :=
      normalizedRadialMellinStrip_bottom_norm_eq
        hd f hnonzero R y
    _ = (Real.exp ((d : ℝ) * Real.log R) *
          Real.pi ^ ((d : ℝ) / 2) *
          (‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ /
            ‖Complex.Gamma
              (((d : ℝ) / 2 : ℝ) +
                Complex.I * (y : ℂ) / 2)‖)) *
          ((radialSurfaceArea d / radialL1Mass f) *
            ‖mellin (radialProfile hd f)
              ((d : ℂ) + Complex.I * (y : ℂ))‖) := by
      rw [hboundary]
      ring
    _ ≤ (Real.exp ((d : ℝ) * Real.log R) *
          Real.pi ^ ((d : ℝ) / 2) *
          (‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ /
            ‖Complex.Gamma
              (((d : ℝ) / 2 : ℝ) +
                Complex.I * (y : ℂ) / 2)‖)) * 1 :=
      mul_le_mul_of_nonneg_left hdual hfactor
    _ = Real.exp
        (((d : ℝ) / 2) * Real.log (Real.pi * R ^ 2) +
          Real.log
            ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ -
          Real.log
            ‖Complex.Gamma
              (((d : ℝ) / 2 : ℝ) +
                Complex.I * (y : ℂ) / 2)‖) := by
      rw [mul_one]
      exact
        (radialGammaBoundaryExponent_exp d R
          ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖
          ‖Complex.Gamma
            (((d : ℝ) / 2 : ℝ) +
              Complex.I * (y : ℂ) / 2)‖
          hR hnum hden).symm
end CohnElkies
