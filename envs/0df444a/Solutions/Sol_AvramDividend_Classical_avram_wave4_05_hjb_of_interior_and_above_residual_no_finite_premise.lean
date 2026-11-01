-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_hjb_of_interior_and_above_residual_no_finite_premise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:36:49.96829+00:00
-- url     : https://prove2.me/submissions/b1f4e5e4-4c38-44a1-b0d2-4a17d2e31faf

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_hjb_of_interior_and_above_residual
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Derive finite cstar; only interior harmonicity and the above-cap residual remain. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hsmooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hres_above : ∀ y : ℝ, (cstar W).toReal < y →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (hinside : 0 < cstar W → ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by
  exact avram_wave4_05_hjb_of_interior_and_above_residual
    X hX q hq W hW (cstar_lt_top X hX q hq W hW)
    hsmooth hres_above hinside
