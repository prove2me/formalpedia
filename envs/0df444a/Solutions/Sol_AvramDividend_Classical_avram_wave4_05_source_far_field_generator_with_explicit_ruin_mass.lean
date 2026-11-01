-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_far_field_generator_with_explicit_ruin_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:08:44.64098+00:00
-- url     : https://prove2.me/submissions/3e91bc14-6339-42f8-96cb-bd2c53452255

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_generator_eq_drift_add_large_tail
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_large_tail_split_at_ruin
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The exact source generator records the strict ruin-crossing mass, while
retaining the atom landing exactly at reserve zero in the surviving tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x =
        X.c + (X.ν.real (Iio (-x)) * (-vcstar W x) +
          ∫ y in Icc (-x) (-1 : ℝ),
            (vcstar W (x + y) - vcstar W x) ∂X.ν) := by
  obtain ⟨hdom, hgen⟩ :=
    avram_wave4_05_source_far_field_generator_eq_drift_add_large_tail
      X q W hW x hfar
  have hsplit :=
    avram_wave4_05_source_far_field_large_tail_split_at_ruin
      X q W hW x hfar
  refine ⟨hdom, ?_⟩
  rw [hgen, hsplit]
