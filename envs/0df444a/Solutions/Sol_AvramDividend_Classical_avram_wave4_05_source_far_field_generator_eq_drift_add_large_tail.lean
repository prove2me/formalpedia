-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_far_field_generator_eq_drift_add_large_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:55:51.092907+00:00
-- url     : https://prove2.me/submissions/a5f00b5c-7517-47c0-9f97-5ff0433d9ee0

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_above_eq_drift_add_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_jump_integral_exact_large_tail
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact original-source generator at high reserves: only drift and
uncompensated negative jumps of magnitude at least one survive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x =
        X.c + ∫ y in Iic (-1 : ℝ),
          (vcstar W (x + y) - vcstar W x) ∂X.ν := by
  have hx : (cstar W).toReal < x := by linarith
  obtain ⟨hdom, htail⟩ :=
    avram_wave4_05_source_far_field_jump_integral_exact_large_tail
      X q W hW x hfar
  refine ⟨hdom, ?_⟩
  rw [vcstar_generator_above_eq_drift_add_jump X W x hx]
  rw [htail]
