-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_real_extension_leftContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:07:30.693018+00:00
-- url     : https://prove2.me/submissions/ff13b4cb-9733-4f84-b0c7-1a8d129d384a

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    ∀ t : ℝ,
      ContinuousWithinAt (fun s : ℝ => D s.toNNReal ω) (Iic t) t := by
  intro t
  have hmap : Set.MapsTo Real.toNNReal (Iic t) (Iic t.toNNReal) := by
    intro s hs
    exact Real.toNNReal_mono hs
  have h :=
    (hD.2.2.1 ω t.toNNReal).comp
      continuous_real_toNNReal.continuousWithinAt hmap
  simpa only [Function.comp_def] using h
