-- Prove2me | solution 1 for AvramDividend.Classical.pure_jump_unbounded_variation_infinite_negative_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:28:32.366999+00:00
-- url     : https://prove2.me/submissions/49ca6aa0-f494-4768-8cb5-ea8a5aa08c15

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_infinite_small_jump_moment_implies_infinite_negative_activity
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0) (hnbv : ¬ X.BoundedVariation) :
    X.ν (Iio (0 : ℝ)) = ⊤ := by
  have hsmall : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤ := by
    by_contra h
    apply hnbv
    exact ⟨hσ, lt_top_iff_ne_top.mpr h⟩
  exact infinite_small_jump_moment_implies_infinite_negative_activity
    X.ν hsmall
