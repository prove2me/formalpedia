-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_hjb_of_bounded_strip_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:26:00.920452+00:00
-- url     : https://prove2.me/submissions/bfeeaf31-7867-476c-bbf9-94f40989760a

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_eventual_hjb_finite_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_or_bv_hjb_residual_only
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Check the genuine upper source residual only on a finite strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hbranch : 0 < X.σ ∨ X.BoundedVariation)
    (hres_strip : ∀ y : ℝ,
      (cstar W).toReal < y →
      y < (cstar W).toReal + 1 + max 0 (X.c / q) →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by
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
  exact avram_wave4_05_gaussian_or_bv_hjb_residual_only
    X hX q hq W hW hbranch hres_all
