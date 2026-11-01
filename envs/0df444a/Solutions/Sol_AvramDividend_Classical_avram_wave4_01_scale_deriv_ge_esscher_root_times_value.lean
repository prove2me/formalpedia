-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_scale_deriv_ge_esscher_root_times_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:22:54.183994+00:00
-- url     : https://prove2.me/submissions/1771f3b8-cde1-4614-9cb0-9969a4ab250c

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The genuine reflected first-record hazard imposes a positive-root
differential growth lower bound on the canonical q-scale function. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ a : ℝ, 0 < a → φ * W a ≤ deriv W a := by
  intro a ha
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hpos : 0 < W a :=
    scaleFunction_strict_pos_of_unbounded_variation
      X q W hW hnbv a ha
  have hrate : φ ≤ deriv W a / W a :=
    avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
      X q hq W hW hvar φ hφ hroot a ha
  exact (le_div_iff₀ hpos).mp hrate
