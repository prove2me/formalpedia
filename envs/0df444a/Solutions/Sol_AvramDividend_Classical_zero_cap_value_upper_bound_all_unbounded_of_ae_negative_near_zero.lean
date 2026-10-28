-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_value_upper_bound_all_unbounded_of_ae_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:16:53.211858+00:00
-- url     : https://prove2.me/submissions/8220a892-0f21-407f-84fb-84a6f023e8aa

import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Arbitrarily early downward paths give the zero-cap upper bound at every
nonnegative starting reserve for an unbounded-variation process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hnbv : ¬ X.BoundedVariation)
    (hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by
  obtain ⟨hvalue, hEq⟩ :=
    barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
      X hX q hq W hW hnbv hNear
  have hzero : valueFunctionLe X q 0 0 ≤
      ENNReal.ofReal (barrierValue W 0 0) :=
    zero_cap_value_at_zero_upper_bound_of_boundary X hX q hq W hEq
  intro x hx
  exact zero_cap_value_upper_bound_of_zero_bound X q W hzero hvalue x hx
