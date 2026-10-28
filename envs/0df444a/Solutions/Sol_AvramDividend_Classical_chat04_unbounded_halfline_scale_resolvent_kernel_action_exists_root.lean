-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_halfline_scale_resolvent_kernel_action_exists_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:44:02.64929+00:00
-- url     : https://prove2.me/submissions/f8f60856-5517-448e-a332-b762cc13afb8

import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_resolvent_kernel_action_exists_root
import Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_convolution_support_restrict
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Full-half-line scale resolvent kernel action for some positive Esscher parameter. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q p : ℝ) (hq : 0 ≤ q) (hp : 0 < p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (hzero : ∀ z : ℝ, z < 0 → Wqp z = 0)
    (x : ℝ) (hx : 0 < x) :
    ∃ θ : ℝ, 0 < θ ∧
      (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * Wq y) * Wqp x -
        (∫ y in Ioi (0 : ℝ), Wq y * Wqp (x - y)) =
      Wq x / p := by
  obtain ⟨θ, hθ, haction⟩ :=
    chat04_unbounded_scale_resolvent_kernel_action_exists_root
      X hnbv q p hq hp Wq Wqp hWq hWqp x hx
  refine ⟨θ, hθ, ?_⟩
  rw [chat04_killed_resolvent_convolution_support_restrict
    x (le_of_lt hx) Wq Wqp hzero]
  exact haction
