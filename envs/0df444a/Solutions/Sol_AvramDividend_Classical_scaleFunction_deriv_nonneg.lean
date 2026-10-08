-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_deriv_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:00:19.319221+00:00
-- url     : https://prove2.me/submissions/214cdf9c-a6c0-49a7-8cdd-43b8f08969bf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) :
    0 ≤ deriv W x := by
  have hm : MonotoneOn W (Set.Ici (0 : ℝ)) := hW.2.2.2.1
  have hn : Set.Ici (0 : ℝ) ∈ 𝓝 x := by
    apply Filter.mem_of_superset (isOpen_Ioi.mem_nhds hx)
    intro y hy
    exact (Set.mem_Ioi.mp hy).le
  simpa only [derivWithin_of_mem_nhds hn] using
    (hm.derivWithin_nonneg (x := x))
