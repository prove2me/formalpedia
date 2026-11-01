-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_hjb_residual_only
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:36:49.624625+00:00
-- url     : https://prove2.me/submissions/fbd350da-d562-46cb-9584-c93fc0131e12

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_or_bv_vcstar_interior_harmonicity
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_hjb_of_interior_and_above_residual
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Full original-source Gaussian/BV HJB from only the above-cap residual inequality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hbranch : 0 < X.σ ∨ X.BoundedVariation)
    (hres_above : ∀ y : ℝ, (cstar W).toReal < y →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by
  have hc := cstar_lt_top X hX q hq W hW
  have hsmooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0) := by
    rcases hbranch with hσ | hbv
    · exact Or.inl hσ
    · exact Or.inr (Or.inl hbv)
  have hinside : 0 < cstar W → ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0 := by
    intro hcpos
    exact avram_wave4_05_gaussian_or_bv_vcstar_interior_harmonicity
      X hX q hq W hW hbranch hcpos
  exact avram_wave4_05_hjb_of_interior_and_above_residual
    X hX q hq W hW hc hsmooth hres_above hinside
