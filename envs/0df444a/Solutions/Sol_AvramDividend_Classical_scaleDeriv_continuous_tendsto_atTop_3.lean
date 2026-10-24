-- Prove2me | solution 3 for AvramDividend.Classical.scaleDeriv_continuous_tendsto_atTop
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:27:43.99877+00:00
-- url     : https://prove2.me/submissions/99f19fdd-bde0-4db4-a345-7d588386a20e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_tendsto_atTop

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The combined scale derivative regularity theorem is the conjunction of
the existing continuity and coercivity obligations.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi 0) ∧
      Filter.Tendsto (deriv W) Filter.atTop Filter.atTop := by
  exact ⟨scaleDeriv_continuous X hX q hq W hW,
    scaleDeriv_tendsto_atTop X hX q hq W hW⟩
