-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_variation_gaussian_or_infinite_small_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:17:23.17773+00:00
-- url     : https://prove2.me/submissions/1493012d-dce1-47bb-a735-1a5e8bbcad8f

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/--
Every spectrally negative Levy process of unbounded variation either
has a strictly positive Gaussian coefficient or infinite first moment
of its small negative jumps.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    0 < X.σ ∨
      (∫⁻ y in Ioo (-1 : ℝ) 0,
        ENNReal.ofReal |y| ∂X.ν) = ⊤ := by
  by_cases hσ : X.σ = 0
  · right
    by_contra hfin
    apply hnbv
    exact ⟨hσ, lt_top_iff_ne_top.mpr hfin⟩
  · left
    exact lt_of_le_of_ne X.σ_nonneg (Ne.symm hσ)
