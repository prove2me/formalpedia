-- Prove2me | solution 1 for CohnElkies.normalizedRadialMellinStrip_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/66c66954-20f3-4fb8-9f76-c79a5033f447

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialProfile_mellin_uniform_strip_bound

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
    (hzero : f (0 : Euclidean d) = 0) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ,
        -((d : ℝ) / 2) ≤ z.im →
        z.im ≤ (d : ℝ) / 2 →
          ‖normalizedRadialMellinStrip hd f R z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    radialProfile_mellin_uniform_strip_bound hd f hf hzero
  let B : ℝ :=
    |radialSurfaceArea d / radialL1Mass f| *
      Real.exp ((d : ℝ) * |Real.log R|) * C
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro z hzlower hzupper
  have hsnonneg :
      0 ≤ (((d : ℂ) / 2 - Complex.I * z).re) := by
    norm_num
    linarith
  have hsupper :
      (((d : ℂ) / 2 - Complex.I * z).re) ≤ (d : ℝ) := by
    norm_num
    linarith
  have hphase :
      ((((d : ℂ) / 2 + Complex.I * z) *
        (Real.log R : ℂ))).re ≤
        (d : ℝ) * |Real.log R| := by
    norm_num
    have hcoefnonneg :
        0 ≤ (d : ℝ) / 2 - z.im := by
      linarith
    have hcoefupper :
        (d : ℝ) / 2 - z.im ≤ (d : ℝ) := by
      linarith
    calc
      ((d : ℝ) / 2 - z.im) * Real.log R ≤
          ((d : ℝ) / 2 - z.im) * |Real.log R| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hcoefnonneg
      _ ≤ (d : ℝ) * |Real.log R| :=
        mul_le_mul_of_nonneg_right hcoefupper (abs_nonneg _)
  change ‖normalizedRadialMellinStrip hd f R z‖ ≤ B
  calc
    ‖normalizedRadialMellinStrip hd f R z‖ =
        |radialSurfaceArea d / radialL1Mass f| *
          Real.exp
            ((((d : ℂ) / 2 + Complex.I * z) *
              (Real.log R : ℂ))).re *
          ‖mellin (radialProfile hd f)
            ((d : ℂ) / 2 - Complex.I * z)‖ := by
      unfold normalizedRadialMellinStrip radialMellinStrip
      rw [norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_exp]
    _ ≤ |radialSurfaceArea d / radialL1Mass f| *
          Real.exp ((d : ℝ) * |Real.log R|) * C := by
      gcongr
      exact hbound _ hsnonneg hsupper
    _ = B := rfl
end CohnElkies
