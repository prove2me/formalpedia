-- Prove2me | solution 11 for AvramDividend.Classical.barrier_cstar_capped_value_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:37:41.977037+00:00
-- url     : https://prove2.me/submissions/0ec23c5c-b776-4720-be3b-b4961e022e8c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_capped_value_upper_bound_of_positive_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0∞) ≤ cstar W) with hz | hp
  · have hc0 : cstar W = 0 := hz.symm
    intro x hx
    have hbound := zero_cap_value_upper_bound X hX q hq W hW x hx
    have hvc : vcstar W x = barrierValue W 0 x := by
      change barrierValue W (cstar W).toReal x = barrierValue W 0 x
      simp [hc0]
    simpa only [hc0, hvc] using hbound
  · exact barrier_cstar_capped_value_upper_bound_of_positive_cstar
      X hX q hq W hW hc hp h_smooth
