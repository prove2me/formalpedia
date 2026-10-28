-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_strict_exit_factor_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:28:07.599393+00:00
-- url     : https://prove2.me/submissions/04611ae7-dac8-4a13-92a7-1b02001aeb1c

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_of_notBV
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_factor_lt_one_of_positive_root
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x < a) :
    twoSidedExitExpectation X q a x < 1 := by
  obtain ⟨φ, hφ, hroot⟩ :=
    unbounded_esscher_root_of_notBV X q hq hnbv
  exact chat04_strict_exit_factor_lt_one_of_positive_root
    X q hq φ hφ hroot a x ha hx hxa
