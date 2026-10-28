-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_value_upper_bound_all_gaussian_of_ae_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:07:28.209001+00:00
-- url     : https://prove2.me/submissions/6ff555a9-9568-4d54-8b29-6a465fd1a928

import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_gaussian_of_ae_negative_near_zero
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Gaussian downward regularity at the origin controls the optimal zero-cap
dividend value at every nonnegative starting reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by
  obtain ⟨hvalue, hEq⟩ :=
    barrier_zero_boundary_value_package_gaussian_of_ae_negative_near_zero
      X hX q hq W hW hσ hNear
  have hzero : valueFunctionLe X q 0 0 ≤
      ENNReal.ofReal (barrierValue W 0 0) :=
    zero_cap_value_at_zero_upper_bound_of_boundary X hX q hq W hEq
  intro x hx
  exact zero_cap_value_upper_bound_of_zero_bound X q W hzero hvalue x hx
