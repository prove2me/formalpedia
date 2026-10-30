-- Prove2me | solution 22 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T07:38:29.819525+00:00
-- url     : https://prove2.me/submissions/c3431218-c3d7-43ee-8f4b-b30ac6e58211
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_bv_standing
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_cstar_finite_of_normalized_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Reduce finite-barrier closure to Standing C1 regularity, using the
proved genuine Esscher monotonicity in the unbounded-variation case. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ := by
  by_cases hBV : X.BoundedVariation
  · exact cstar_lt_top_of_bv_standing X hX q hq W hW hBV
  · have hreg : ContDiffOn ℝ 1 W (Ioi 0) :=
      scaleFunction_contDiff_one_of_standing X hX q hq W hW
    obtain ⟨hpos, φ, hφ, htilt⟩ :=
      unbounded_tilted_positive_monotone X q hq W hW hBV
    have hW1 : 0 < W 1 := hpos 1 (by norm_num)
    have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
      intro x hx
      exact (hreg.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds hx)
    have hcont : ContinuousOn (deriv W) (Ioi 0) :=
      hreg.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
    exact cstar_finite_of_normalized_monotone
      W φ hφ hW1 htilt hdiff hcont
