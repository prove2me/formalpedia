-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_inf_attained
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T21:32:56.405984+00:00
-- url     : https://prove2.me/submissions/7726f44a-4c0a-43c7-a331-600769b46b64
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_continuous_pos_infimum_dichotomy
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_tendsto_atTop

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → deriv W a ≤ deriv W x) ∨
      ∀ x : ℝ, 0 < x → derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by
  have hreg := scaleDeriv_continuous_tendsto_atTop X hX q hq W hW
  have hdich :=
    continuous_pos_infimum_dichotomy (deriv W) hreg.1 hreg.2
  change
    (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → deriv W a ≤ deriv W x) ∨
      ∀ x : ℝ, 0 < x →
        Filter.liminf (fun y => ((deriv W y : ℝ) : EReal)) (𝓝[>] (0 : ℝ)) ≤
          ((deriv W x : ℝ) : EReal)
  exact hdich
