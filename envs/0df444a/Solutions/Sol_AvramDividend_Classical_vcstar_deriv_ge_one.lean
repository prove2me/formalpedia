-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_ge_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T23:51:59.565314+00:00
-- url     : https://prove2.me/submissions/f44785ad-ee79-4536-9183-4998d3f506df
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_cstar_finite_zero_or_deriv_minimal
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_regular_minimal

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (vcstar W) x ∧
      1 ≤ deriv (vcstar W) x := by
  have hreg := scaleFunction_contDiff_one X hX q hq W hW
  have hpos := scaleDeriv_pos X hX q hq W hW
  have hmin := (cstar_finite_zero_or_deriv_minimal X hX q hq W hW).2
  exact vcstar_deriv_ge_one_of_regular_minimal W hreg hpos hmin
