-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_ruin_crossing_jump_integral_eq_tail_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:02:01.211203+00:00
-- url     : https://prove2.me/submissions/63a229ca-70bb-4ec8-91c2-b651ea9ae7b9

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The strict ruin-crossing source jump integral is the exact pre-jump
value multiplied by the real mass of jumps exceeding the reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (x : ℝ)
    (hfar : (cstar W).toReal + 1 ≤ x) :
    (∫ y in Iio (-x),
      SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν) =
      X.ν.real (Iio (-x)) * (-vcstar W x) := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hx1 : 1 ≤ x := by dsimp [a] at *; linarith
  have hon : Set.EqOn
      (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x)
      (fun _ : ℝ => -vcstar W x)
      (Iio (-x)) := by
    intro y hy
    have hruin : y < -x := hy
    have hyneg : y < 0 := by linarith
    have hlarge : y ≤ -1 := by linarith
    have hxyneg : x + y < 0 := by linarith
    have hz : vcstar W (x + y) = 0 := by
      change barrierValue W a (x + y) = 0
      simp [barrierValue, hxyneg]
    rw [avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel
      W x y hfar hyneg, if_pos hlarge, hz]
    simp
  rw [setIntegral_congr_fun measurableSet_Iio hon]
  simp
