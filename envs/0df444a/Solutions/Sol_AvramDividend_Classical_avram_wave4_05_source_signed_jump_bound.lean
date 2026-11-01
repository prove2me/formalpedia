-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_signed_jump_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:12:11.141463+00:00
-- url     : https://prove2.me/submissions/603f692f-690b-400e-8ab4-b4053f9dbec7

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_all_cap_positive_jump_part_exact
import Mathlib.Algebra.Notation.Indicator
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The signed original compensated jump kernel has an exact negative
large-ruin correction, even when the optimal cap is zero. Unlike an estimate
by its positive part, this retains the killing effect of sufficiently large
downward jumps. The strict landing boundary is excluded deliberately. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x)
    (y : ℝ) (hy : y < 0) :
    SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ≤
      (if y ∈ Ioo (-1 : ℝ) (-x) then max 0 (-vcstar W x - y) else 0) -
      (if y ∈ Iic (-1 : ℝ) ∩ Iio (-x) then vcstar W x else 0) := by
  by_cases htail : y ∈ Iic (-1 : ℝ) ∩ Iio (-x)
  · have hy1 : y ≤ -1 := htail.1
    have hyx : y < -x := htail.2
    have hxy : x + y < 0 := by linarith
    have hnot : y ∉ Ioo (-1 : ℝ) 1 := by
      intro hmem
      exact (not_lt_of_ge hy1) hmem.1
    have hcross : y ∉ Ioo (-1 : ℝ) (-x) := by
      intro hmem
      exact (not_lt_of_ge hy1) hmem.1
    have hzero : vcstar W (x + y) = 0 := by
      change barrierValue W (cstar W).toReal (x + y) = 0
      simp [barrierValue, hxy]
    simp only [if_neg hcross, if_pos htail, zero_sub]
    unfold SpectrallyNegativeLevy.generatorIntegrand
    simp [Set.indicator_of_notMem hnot, hzero]
  · have hpos := avram_wave4_05_source_all_cap_positive_jump_part_exact
      X hX q hq W hW x hx y hy
    have hle :
        SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ≤
          max 0 (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y) :=
      le_max_right _ _
    simpa only [if_neg htail, sub_zero, hpos] using hle
