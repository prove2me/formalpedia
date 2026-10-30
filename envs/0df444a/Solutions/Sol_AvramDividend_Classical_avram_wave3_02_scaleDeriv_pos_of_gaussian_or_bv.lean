-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_scaleDeriv_pos_of_gaussian_or_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:18:22.558673+00:00
-- url     : https://prove2.me/submissions/0984c092-a3e7-4b7c-ae82-0c6723920b1a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Source q-scale derivative positivity in both already regular Lévy branches. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbranch : 0 < X.σ ∨ X.BoundedVariation) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by
  have hC1 : ContDiffOn ℝ 1 W (Ioi 0) := by
    rcases hbranch with hσ | hBV
    · exact scaleFunction_contDiff_one_of_gaussian X hX q hq W hW hσ
    · exact scaleFunction_contDiffOn_one_of_boundedVariation X hX q hq W hW hBV
  have hdiffOn : DifferentiableOn ℝ W (Ioi 0) :=
    ContDiffOn.differentiableOn_one hC1
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact hdiffOn.differentiableAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hx))
  obtain ⟨hpos, htilt⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  exact scaleDeriv_pos_of_tilted_positive_monotone
    X hX q hq W hW hpos hdiff htilt
