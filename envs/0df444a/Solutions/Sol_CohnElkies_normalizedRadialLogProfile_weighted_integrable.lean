-- Prove2me | solution 1 for CohnElkies.normalizedRadialLogProfile_weighted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/a4742434-906e-4122-afba-e7ad348c566b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialProfile_mellinConvergent
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
    (hd : 0 < d) (f : TestFunction d)
    (hf : IsRadial f) (hreal : IsRealValued f)
    (hzero : f (0 : Euclidean d) = 0)
    {R : ℝ} (hR : 0 < R) {a : ℝ}
    (ha : a < (d : ℝ) + 2) :
    Integrable (fun v : ℝ =>
      (Real.exp (-a * v) : ℂ) *
        (normalizedRadialLogProfile hd f R v : ℂ)) := by
  let κ : ℝ := (d : ℝ) - a
  have hκ : -2 < κ := by
    try dsimp [κ]
    linarith
  have hconv : MellinConvergent
      (radialProfile hd f) (κ : ℂ) := by
    apply radialProfile_mellinConvergent hd f hf hzero
    simpa using! hκ
  have hscaled : MellinConvergent
      (fun r : ℝ => radialProfile hd f (R * r)) (κ : ℂ) :=
    (MellinConvergent.comp_mul_left hR).mpr hconv
  have hchange : Integrable (fun v : ℝ =>
      (1 * Real.exp v) •
        (((1 * Real.exp v : ℝ) : ℂ) ^
          ((κ : ℂ) - 1) •
            radialProfile hd f (R * (1 * Real.exp v)))) := by
    apply (integrable_scaled_exp_change_Ioi
      (R := (1 : ℝ)) (by norm_num)
      (fun r : ℝ =>
        (r : ℂ) ^ ((κ : ℂ) - 1) •
          radialProfile hd f (R * r))).mp
    exact hscaled
  have hpower (v : ℝ) :
      (Real.exp v : ℂ) *
        (Real.exp v : ℂ) ^ ((κ : ℂ) - 1) =
          (Real.exp (κ * v) : ℂ) := by
    have hbase : (Real.exp v : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero v)
    calc
      (Real.exp v : ℂ) *
          (Real.exp v : ℂ) ^ ((κ : ℂ) - 1) =
        (Real.exp v : ℂ) ^ (1 : ℂ) *
          (Real.exp v : ℂ) ^ ((κ : ℂ) - 1) := by
        rw [Complex.cpow_one]
      _ = (Real.exp v : ℂ) ^
          ((1 : ℂ) + ((κ : ℂ) - 1)) := by
        rw [Complex.cpow_add _ _ hbase]
      _ =
        (Real.exp v : ℂ) ^ (κ : ℂ) := by
        congr 1
        ring
      _ = (Real.exp (κ * v) : ℂ) := by
        rw [Complex.cpow_def_of_ne_zero hbase,
          ← Complex.ofReal_log (Real.exp_pos v).le,
          Real.log_exp, Complex.ofReal_exp]
        congr 1
        push_cast
        ring
  have hplus : Integrable (fun v : ℝ =>
      (Real.exp (κ * v) : ℂ) *
        radialProfile hd f (R * Real.exp v)) := by
    apply hchange.congr
    filter_upwards [] with v
    simp only [one_mul, smul_eq_mul, Complex.real_smul]
    rw [← mul_assoc, hpower]
  have hfactor :=
    hplus.const_mul
      ((radialSurfaceArea d / radialL1Mass f * R ^ d : ℝ) : ℂ)
  apply hfactor.congr
  filter_upwards [] with v
  rw [normalizedRadialLogProfile_weighted_ofReal
    hd f hreal R a v]
  try dsimp [κ]
  ring
end CohnElkies
