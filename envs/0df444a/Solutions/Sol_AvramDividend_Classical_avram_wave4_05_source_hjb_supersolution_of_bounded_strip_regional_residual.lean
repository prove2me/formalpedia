-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_hjb_supersolution_of_bounded_strip_regional_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:25:18.640089+00:00
-- url     : https://prove2.me/submissions/2a94f710-b2d5-465c-9447-14f7b8665279

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_eventual_hjb_finite_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_original_source_hjb_supersolution_of_interior_superharmonicity
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Full compensated-generator supersolution from two bounded regional tests. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hsmooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hres_strip : ∀ y : ℝ,
      (cstar W).toReal < y →
      y < (cstar W).toReal + 1 + max 0 (X.c / q) →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (hinside_super : 0 < cstar W → ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) ≤ 0 := by
  have hcfin := cstar_lt_top X hX q hq W hW
  have hres_all : ∀ y : ℝ, (cstar W).toReal < y →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0 := by
    intro y hy
    by_cases hnear : y < (cstar W).toReal + 1 + max 0 (X.c / q)
    · exact hres_strip y hy hnear
    · have hfar : (cstar W).toReal + 1 + max 0 (X.c / q) ≤ y :=
        le_of_not_gt hnear
      have hHJB := vcstar_eventual_hjb_finite_cstar
        X hX q hq W hW hcfin y hfar
      exact le_trans (le_max_left _ _) (le_of_eq hHJB.2)
  exact avram_wave4_05_original_source_hjb_supersolution_of_interior_superharmonicity
    X hX q hq W hW hsmooth hres_all hinside_super
