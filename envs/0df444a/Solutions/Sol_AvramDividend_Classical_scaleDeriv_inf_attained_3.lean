-- Prove2me | solution 3 for AvramDividend.Classical.scaleDeriv_inf_attained
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-18T18:51:30.859833+00:00
-- url     : https://prove2.me/submissions/33763130-72aa-4488-b161-603d82c72102
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Order.LiminfLimsup
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_tendsto_atTop
import Theorems.Thm_AvramDividend_Classical_continuous_pos_infimum_dichotomy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact published `scaleDeriv_inf_attained` target. This bypasses
    the intermediate bundled `scaleDeriv_continuous_tendsto_atTop` child.
    Both real regularity/growth inputs remain Open in the dated snapshot. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → deriv W a ≤ deriv W x) ∨
      ∀ x : ℝ, 0 < x →
        derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by
  have hcont : ContinuousOn (deriv W) (Ioi 0) :=
    scaleDeriv_continuous X hX q hq W hW
  have htop : Tendsto (deriv W) atTop atTop :=
    scaleDeriv_tendsto_atTop X hX q hq W hW
  simpa only [derivZeroPlus] using
    (continuous_pos_infimum_dichotomy (deriv W) hcont htop)
