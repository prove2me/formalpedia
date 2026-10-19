-- Prove2me | solution 1 for CohnElkies.normalizedRadialMellinStrip_shifted_eq_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/34e97e67-c190-4abc-bf3e-ee830400e084

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedRadialLogProfile_weighted_ofReal

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
    (hd : 0 < d) (f : TestFunction d) (hreal : IsRealValued f)
    (R : ℝ) (hR : 0 < R) (a t : ℝ) :
    normalizedRadialMellinStrip hd f R
        ((t : ℂ) + Complex.I *
          ((((d : ℝ) / 2 - a : ℝ) : ℂ))) =
      (𝓕 (fun v : ℝ =>
        (Real.exp (-a * v) : ℂ) *
          (normalizedRadialLogProfile hd f R v : ℂ)) :
          ℝ → ℂ) (t / (2 * Real.pi)) := by
  let s : ℂ := (((d : ℝ) - a : ℝ) : ℂ) -
    Complex.I * (t : ℂ)
  let g : ℝ → ℂ := fun u =>
    Real.exp (-((d : ℝ) - a) * u) •
      radialProfile hd f (R * Real.exp (-u))
  let c : ℂ :=
    ((radialSurfaceArea d / radialL1Mass f * R ^ d : ℝ) : ℂ)
  have hweight :
      (fun v : ℝ =>
        (Real.exp (-a * v) : ℂ) *
          (normalizedRadialLogProfile hd f R v : ℂ)) =
        c • (fun v : ℝ => g (-v)) := by
    funext v
    have hv :=
      normalizedRadialLogProfile_weighted_ofReal
        hd f hreal R a v
    change _ = c * g (-v)
    calc
      (Real.exp (-a * v) : ℂ) *
          (normalizedRadialLogProfile hd f R v : ℂ) =
          ((radialSurfaceArea d / radialL1Mass f * R ^ d : ℝ) : ℂ) *
            (Real.exp (((d : ℝ) - a) * v) : ℂ) *
            radialProfile hd f (R * Real.exp v) := hv
      _ = c * g (-v) := by
        simp [c, g, Complex.real_smul, mul_neg]
        ring_nf
  have hmellin :
      mellin (fun r : ℝ => radialProfile hd f (R * r)) s =
        (𝓕 g : ℝ → ℂ) (-(t / (2 * Real.pi))) := by
    simpa [s, g, neg_div] using!
      (mellin_eq_fourier
        (fun r : ℝ => radialProfile hd f (R * r))
        (s := s))
  have hscalar (F : ℝ → ℂ) (x : ℝ) :
      (𝓕 (c • F) : ℝ → ℂ) x =
        c * (𝓕 F : ℝ → ℂ) x := by
    rw [Real.fourier_real_eq_integral_exp_smul,
      Real.fourier_real_eq_integral_exp_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    ring
  have hfourier :
      (𝓕 (fun v : ℝ =>
        (Real.exp (-a * v) : ℂ) *
          (normalizedRadialLogProfile hd f R v : ℂ)) :
          ℝ → ℂ) (t / (2 * Real.pi)) =
        c * mellin (fun r : ℝ =>
          radialProfile hd f (R * r)) s := by
    calc
      (𝓕 (fun v : ℝ =>
        (Real.exp (-a * v) : ℂ) *
          (normalizedRadialLogProfile hd f R v : ℂ)) :
          ℝ → ℂ) (t / (2 * Real.pi)) =
          c * (𝓕 (fun v : ℝ => g (-v)) :
            ℝ → ℂ) (t / (2 * Real.pi)) := by
        rw [hweight,
          hscalar (fun v : ℝ => g (-v))]
      _ = c * (𝓕 g : ℝ → ℂ)
            (-(t / (2 * Real.pi))) := by
        congr 1
        rw [← Real.fourierInv_eq_fourier_comp_neg g,
          Real.fourierInv_eq_fourier_neg]
      _ = c * mellin (fun r : ℝ =>
          radialProfile hd f (R * r)) s := by
        rw [hmellin]
  have hRcomplex : (R : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hR.ne'
  have hRpow :
      ((R ^ d : ℝ) : ℂ) = (R : ℂ) ^ (d : ℂ) := by
    push_cast
    rw [Complex.cpow_natCast]
  have hpower :
      ((R ^ d : ℝ) : ℂ) * (R : ℂ) ^ (-s) =
        Complex.exp
          ((((a : ℂ) + Complex.I * (t : ℂ)) *
            (Real.log R : ℂ))) := by
    rw [hRpow, ← Complex.cpow_add _ _ hRcomplex,
      Complex.cpow_def_of_ne_zero hRcomplex,
      ← Complex.ofReal_log hR.le]
    congr 1
    try dsimp [s]
    push_cast
    ring
  have hscale :
      c * mellin (fun r : ℝ =>
        radialProfile hd f (R * r)) s =
      ((radialSurfaceArea d / radialL1Mass f : ℝ) : ℂ) *
        Complex.exp
          ((((a : ℂ) + Complex.I * (t : ℂ)) *
            (Real.log R : ℂ))) *
        mellin (radialProfile hd f) s := by
    rw [mellin_comp_mul_left
      (radialProfile hd f) s hR]
    simp only [smul_eq_mul]
    try dsimp [c]
    push_cast
    have hc := hpower
    push_cast at hc
    linear_combination
      (((radialSurfaceArea d : ℝ) : ℂ) /
        ((radialL1Mass f : ℝ) : ℂ) *
          mellin (radialProfile hd f) s) * hc
  have harg :
      (d : ℂ) / 2 - Complex.I *
        ((t : ℂ) + Complex.I *
          ((((d : ℝ) / 2 - a : ℝ) : ℂ))) = s := by
    try dsimp [s]
    push_cast
    simp [mul_add, ← mul_assoc, Complex.I_mul_I]; ring
  have hphase :
      (d : ℂ) / 2 + Complex.I *
        ((t : ℂ) + Complex.I *
          ((((d : ℝ) / 2 - a : ℝ) : ℂ))) =
        (a : ℂ) + Complex.I * (t : ℂ) := by
    push_cast
    simp [mul_add, ← mul_assoc, Complex.I_mul_I]; ring
  unfold normalizedRadialMellinStrip radialMellinStrip
  rw [harg, hphase]
  exact hscale.symm.trans hfourier.symm
end CohnElkies
