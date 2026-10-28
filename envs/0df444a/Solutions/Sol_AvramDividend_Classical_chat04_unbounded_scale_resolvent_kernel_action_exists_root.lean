-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_scale_resolvent_kernel_action_exists_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:06:25.716488+00:00
-- url     : https://prove2.me/submissions/378ec793-7697-42a0-83f0-c75c74a88323

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_resolvent_kernel_action
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Select a positive Esscher root and evaluate the killed-resolvent scale kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q p : ℝ) (hq : 0 ≤ q) (hp : 0 < p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (x : ℝ) (hx : 0 < x) :
    ∃ θ : ℝ, 0 < θ ∧
      (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * Wq y) * Wqp x -
        (∫ s in Ioc (0 : ℝ) x, Wq s * Wqp (x - s)) =
      Wq x / p := by
  have hqp : 0 < q + p := by linarith
  obtain ⟨θ, hθ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hnbv (q + p) hqp
  refine ⟨θ, hθ, ?_⟩
  exact chat04_unbounded_scale_resolvent_kernel_action
    X hnbv q p θ hq hp (le_of_lt hθ) hroot Wq Wqp hWq hWqp x hx
