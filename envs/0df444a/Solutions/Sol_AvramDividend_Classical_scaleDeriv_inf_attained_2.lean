-- Prove2me | solution 2 for AvramDividend.Classical.scaleDeriv_inf_attained
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T21:33:00.125288+00:00
-- url     : https://prove2.me/submissions/5943e891-387b-43da-b9a1-fd25b40a414e
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
  rcases scaleDeriv_continuous_tendsto_atTop X hX q hq W hW with ⟨hcont, htop⟩
  simpa [derivZeroPlus] using
    (continuous_pos_infimum_dichotomy (deriv W) hcont htop)
