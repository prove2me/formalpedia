-- Prove2me | solution 4 for AvramDividend.Classical.zero_cap_value_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:22:26.803106+00:00
-- url     : https://prove2.me/submissions/e612c539-5925-47e2-8536-5c81e6491977
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_zero_cap_boundary_value_package
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Reduce the all-reserve zero-cap upper bound to its zero-reserve boundary identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by
  obtain ⟨hval, hzero⟩ := zero_cap_boundary_value_package X hX q hq W hW
  intro x hx
  exact zero_cap_value_upper_bound_of_zero_bound X q W hzero hval x hx
