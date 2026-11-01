-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_scale_deriv_strict_pos_pure_small_jumps_without_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:26:45.995128+00:00
-- url     : https://prove2.me/submissions/027698a5-201d-4e6c-8a65-759b08aa9fe5

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The positive Laplace root yields a strictly positive reflected-record
hazard and hence a strictly positive ordinary q-scale derivative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ∀ a : ℝ, 0 < a → 0 < deriv W a := by
  intro a ha
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hnbv q hq
  have hpos : 0 < W a :=
    scaleFunction_strict_pos_of_unbounded_variation
      X q W hW hnbv a ha
  have hrate : φ ≤ deriv W a / W a :=
    avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
      X q hq W hW hvar φ hφ hroot a ha
  have hmul : φ * W a ≤ deriv W a :=
    (le_div_iff₀ hpos).mp hrate
  exact lt_of_lt_of_le (mul_pos hφ hpos) hmul
