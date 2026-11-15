-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB68_original_upperstrip_discounted_physical_gaussian_source_drift_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:16:49.840204+00:00
-- url     : https://prove2.me/submissions/6fb32239-9116-460f-80c1-68b8fcf2ff61

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB67_original_caplinear_upper_strip_physical_centered_gaussian_source_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m i : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let Y : ℝ := x + X.X s ω - rightLimit D s ω
    let Z : ℝ := x + X.X (s + Δ) ω - rightLimit D s ω
    let V : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    let centred : ℝ :=
      X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
    b < Y → b < Z →
      Real.exp (-(q * (s : ℝ))) * (V Z - V Y - centred) ≤
        Real.exp (-(q * (s : ℝ))) * (Δ : ℝ) * max X.c 0 := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let Y : ℝ := x + X.X s ω - rightLimit D s ω
  let Z : ℝ := x + X.X (s + Δ) ω - rightLimit D s ω
  let V : ℝ → ℝ := fun y =>
    if y ≤ b then w y else w b + (y - b)
  let centred : ℝ :=
    X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
  change b < Y → b < Z →
    Real.exp (-(q * (s : ℝ))) * (V Z - V Y - centred) ≤
      Real.exp (-(q * (s : ℝ))) * (Δ : ℝ) * max X.c 0
  intro hy hz
  have hSource :=
    avram_gbB67_original_caplinear_upper_strip_physical_centered_gaussian_source_drift
      X x b w D ω n m i hy hz
  change V Z - V Y - centred = (Δ : ℝ) * X.c at hSource
  rw [hSource]
  have hΔ : 0 ≤ (Δ : ℝ) := NNReal.coe_nonneg Δ
  have hExp : 0 ≤ Real.exp (-(q * (s : ℝ))) :=
    le_of_lt (Real.exp_pos _)
  calc
    Real.exp (-(q * (s : ℝ))) * ((Δ : ℝ) * X.c) =
        (Real.exp (-(q * (s : ℝ))) * (Δ : ℝ)) * X.c := by ring
    _ ≤ (Real.exp (-(q * (s : ℝ))) * (Δ : ℝ)) * max X.c 0 :=
      mul_le_mul_of_nonneg_left (le_max_left X.c 0)
        (mul_nonneg hExp hΔ)
    _ = Real.exp (-(q * (s : ℝ))) * (Δ : ℝ) * max X.c 0 := by ring
