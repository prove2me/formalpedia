-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_zero_cap_positive_jump_part_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:31:27.686423+00:00
-- url     : https://prove2.me/submissions/4b2326c5-8d5d-41c5-94e2-ed851d971432

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_zero_cap_positive_jump_kernel_support
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
import Mathlib.Algebra.Notation.Indicator
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The exact positive part of the original compensated jump kernel
at a zero optimal dividend cap is the strict small-ruin overshoot. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc0 : cstar W = 0)
    (x : ℝ) (hx : 0 < x)
    (y : ℝ) (hy : y < 0) :
    max 0 (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y) =
      if y ∈ Ioo (-1 : ℝ) (-x)
      then max 0 (-vcstar W x - y) else 0 := by
  by_cases hcross : y ∈ Ioo (-1 : ℝ) (-x)
  · have hy1 : -1 < y := hcross.1
    have hruin : x + y < 0 := by linarith [hcross.2]
    have hmem : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy1, by linarith⟩
    have hzero : vcstar W (x + y) = 0 := by
      change barrierValue W (cstar W).toReal (x + y) = 0
      simp [barrierValue, hruin]
    have hgrad := vcstar_deriv_eq_one_above_cstar W x
      (by simpa [hc0] using hx)
    unfold SpectrallyNegativeLevy.generatorIntegrand
    simp only [Set.indicator_of_mem hmem, Pi.one_apply]
    rw [hzero, hgrad]
    simp [hcross, one_mul, mul_one]
  · have hg :
        SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ≤ 0 :=
      avram_wave4_05_source_zero_cap_positive_jump_kernel_support
        X hX q hq W hW hc0 x hx y hy hcross
    simp [hcross, max_eq_left hg]
