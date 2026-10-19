-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_of_stopped_renewal_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T10:44:56.943507+00:00
-- url     : https://prove2.me/submissions/b4bea437-aba6-4af3-9125-7f2caded12a4

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_reflected_reward_of_renewal_finite_difference_sandwich
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0)
    (hLo : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal
        (ε * W (a - ε) / (W a - W (a - ε))) ≤
          barrierSupValue X a q)
    (hHi : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      barrierSupValue X a q ≤ ENNReal.ofReal
        (ε * W (a + ε) / (W (a + ε) - W a))) :
    barrierSupValue X a q =
      ENNReal.ofReal (W a / deriv W a) := by
  exact reflected_reward_of_renewal_finite_difference_sandwich
    W a (deriv W a) hD hd (barrierSupValue X a q) hLo hHi
