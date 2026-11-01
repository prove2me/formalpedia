-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_original_upper_generator_iff_bounded_strip_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:37:56.167357+00:00
-- url     : https://prove2.me/submissions/556eff31-afbd-4f21-9f90-4d4de6261dc2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_eventual_hjb_finite_cstar
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The root's full source upper generator hypothesis is exactly a bounded strip test. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    (∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) ↔
    (∀ y : ℝ, (cstar W).toReal < y →
      y < (cstar W).toReal + 1 + max 0 (X.c / q) →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0) := by
  constructor
  · intro hfull y hy _
    exact (hfull y hy).2
  · intro hstrip y hy
    have hint := vcstar_generatorIntegrable_strictly_above_real_cstar
      X q W hW y hy
    refine ⟨hint, ?_⟩
    by_cases hnear : y < (cstar W).toReal + 1 + max 0 (X.c / q)
    · exact hstrip y hy hnear
    · have hfar : (cstar W).toReal + 1 + max 0 (X.c / q) ≤ y :=
        le_of_not_gt hnear
      have hcfin := cstar_lt_top X hX q hq W hW
      have hHJB := vcstar_eventual_hjb_finite_cstar
        X hX q hq W hW hcfin y hfar
      exact le_trans (le_max_left _ _) (le_of_eq hHJB.2)
