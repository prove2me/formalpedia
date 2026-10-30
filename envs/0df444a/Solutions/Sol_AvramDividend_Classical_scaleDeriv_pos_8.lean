-- Prove2me | solution 8 for AvramDividend.Classical.scaleDeriv_pos
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:20:31.230282+00:00
-- url     : https://prove2.me/submissions/16e0e8c1-8498-4c07-8d0c-8b5b76426cf2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_infinite_variation_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every variation regime supplies positive-axis differentiability and Esscher positivity. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by
  have hC1 : ContDiffOn ℝ 1 W (Ioi 0) := by
    by_cases hσ : 0 < X.σ
    · exact scaleFunction_contDiff_one_of_gaussian X hX q hq W hW hσ
    · by_cases hBV : X.BoundedVariation
      · exact scaleFunction_contDiffOn_one_of_boundedVariation X hX q hq W hW hBV
      · have hσ0 : X.σ = 0 :=
          le_antisymm (le_of_not_gt hσ) X.σ_nonneg
        have hInf : ∫⁻ y in Ioo (-1 : ℝ) 0,
            ENNReal.ofReal |y| ∂X.ν = ⊤ := by
          by_contra hne
          exact hBV ⟨hσ0, lt_top_iff_ne_top.mpr hne⟩
        exact scaleFunction_contDiff_one_infinite_variation_without_standing
          X q hq W hW hInf
  have hdiffOn : DifferentiableOn ℝ W (Ioi 0) :=
    ContDiffOn.differentiableOn_one hC1
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact hdiffOn.differentiableAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hx))
  obtain ⟨hpos, htilt⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  exact scaleDeriv_pos_of_tilted_positive_monotone
    X hX q hq W hW hpos hdiff htilt
