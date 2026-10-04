-- Prove2me | solution 1 for AvramDividend.Classical.finite_negative_large_jump_mass
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:19:10.601815+00:00
-- url     : https://prove2.me/submissions/590b4d07-df38-48b4-a695-57af1a91bba0

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

open MeasureTheory Set in
theorem solution (ν : Measure ℝ)
    (hν : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    ν (Iic (-1 : ℝ)) < ⊤ := by
  have hpt : ∀ y ∈ Iic (-1 : ℝ), (1 : ℝ≥0∞) ≤ ENNReal.ofReal (min 1 (y ^ 2)) := by
    intro y hy
    have hy' : y ≤ -1 := hy
    have h1 : (1 : ℝ) ≤ y ^ 2 := by nlinarith
    rw [min_eq_left h1, ENNReal.ofReal_one]
  calc ν (Iic (-1 : ℝ)) = ∫⁻ _ in Iic (-1 : ℝ), (1 : ℝ≥0∞) ∂ν := by
        rw [setLIntegral_const, one_mul]
    _ ≤ ∫⁻ y in Iic (-1 : ℝ), ENNReal.ofReal (min 1 (y ^ 2)) ∂ν :=
        setLIntegral_mono' measurableSet_Iic hpt
    _ ≤ ∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν := setLIntegral_le_lintegral _ _
    _ < ⊤ := hν
