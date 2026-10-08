-- Prove2me | solution 3 for AvramDividend.Classical.barrier_strategy_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:25:13.354994+00:00
-- url     : https://prove2.me/submissions/9dfe1975-094d-4f0d-9acc-58c39cc46c8c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_boundary_value
import Theorems.Thm_AvramDividend_Classical_barrier_value_scale_factor
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_ennreal_scale_ratio_cancel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (W x / deriv W a) := by
  obtain ⟨hWa, hscale⟩ :=
    AvramDividend.Classical.barrier_value_scale_factor
      X hX q hq W hW a ha x hx0 hxa
  have hboundary :
      dividendValue X q a (barrierStrategy X a a) =
        ENNReal.ofReal (W a / deriv W a) :=
    AvramDividend.Classical.barrier_boundary_value X hX q hq W hW a ha
  have hderiv : 0 < deriv W a :=
    AvramDividend.Classical.scaleDeriv_pos X hX q hq W hW a ha
  have hx : 0 ≤ W x := hW.2.1 x hx0
  rw [hscale, hboundary]
  exact AvramDividend.Classical.ennreal_scale_ratio_cancel
    (W x) (W a) (deriv W a) hx hWa hderiv
