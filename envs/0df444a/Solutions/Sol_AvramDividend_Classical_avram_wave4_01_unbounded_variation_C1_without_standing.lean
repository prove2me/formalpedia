-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_unbounded_variation_C1_without_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:16:01.434553+00:00
-- url     : https://prove2.me/submissions/28c6adf3-e5de-44e8-aa33-edba838bfbf2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_infinite_variation_without_standing
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Both mechanisms of unbounded variation yield genuine Standing-free
C1 regularity of the original q-scale function on positive reserves. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ContDiffOn ℝ 1 W (Set.Ioi (0 : ℝ)) := by
  by_cases hσ : 0 < X.σ
  · exact scaleFunction_contDiff_one_gaussian_without_standing
      X q hq W hW hσ
  · have hσzero : X.σ = 0 :=
      le_antisymm (le_of_not_gt hσ) X.σ_nonneg
    have hvar :
        ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν = ⊤ := by
      by_contra hnot
      have hfinite :
          ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν < ⊤ :=
        lt_top_iff_ne_top.mpr hnot
      exact hnbv ⟨hσzero, hfinite⟩
    exact scaleFunction_contDiff_one_infinite_variation_without_standing
      X q hq W hW hvar
