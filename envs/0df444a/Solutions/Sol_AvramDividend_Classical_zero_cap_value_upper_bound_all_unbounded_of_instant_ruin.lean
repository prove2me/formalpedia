-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_value_upper_bound_all_unbounded_of_instant_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:26:09.015112+00:00
-- url     : https://prove2.me/submissions/b851bac6-b8cc-437c-bf2f-292e2ccebdf6

import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_of_unbounded_instant_ruin
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Almost-sure instantaneous zero-barrier ruin yields global zero-cap
verification in the unbounded-variation regime. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hnbv : ¬ X.BoundedVariation)
    (hRuin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by
  obtain ⟨hval, hboundary⟩ :=
    barrier_zero_boundary_value_package_of_unbounded_instant_ruin
      X hX q hq W hW hnbv hRuin
  have hzero : valueFunctionLe X q 0 0 ≤
      ENNReal.ofReal (barrierValue W 0 0) :=
    zero_cap_value_at_zero_upper_bound_of_boundary X hX q hq W hboundary
  intro x hx
  exact zero_cap_value_upper_bound_of_zero_bound X q W hzero hval x hx
