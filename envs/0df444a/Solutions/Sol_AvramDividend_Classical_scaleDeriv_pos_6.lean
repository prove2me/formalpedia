-- Prove2me | solution 6 for AvramDividend.Classical.scaleDeriv_pos
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:32:41.857494+00:00
-- url     : https://prove2.me/submissions/3c3e4a21-6694-4d9d-9b54-59dfdf2a4efe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! Strict derivative positivity from scale positivity, C¹ regularity and tilt. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by
  have hpos : ∀ x : ℝ, 0 < x → 0 < W x :=
    fun x hx => scaleFunction_strict_pos_of_standing X hX q hq W hW x hx
  have hC1 : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hC1.differentiableOn_one x hx).differentiableAt
      (isOpen_Ioi.mem_nhds hx)
  have htilt :=
    (scaleFunction_tilted_positive_monotone X hX q hq W hW).2
  exact scaleDeriv_pos_of_tilted_positive_monotone
    X hX q hq W hW hpos hdiff htilt
