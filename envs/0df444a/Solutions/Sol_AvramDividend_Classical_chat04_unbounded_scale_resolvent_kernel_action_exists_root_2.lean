-- Prove2me | solution 2 for AvramDividend.Classical.chat04_unbounded_scale_resolvent_kernel_action_exists_root
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:06:58.534506+00:00
-- url     : https://prove2.me/submissions/72ef4066-3602-468c-9a7a-09ae081eb81b

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_resolvent_kernel_action

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
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
  obtain ⟨φ, hφ, hroot⟩ := positive_esscher_root_of_unbounded_variation X hnbv (q + p) (by linarith)
  exact ⟨φ, hφ, chat04_unbounded_scale_resolvent_kernel_action X hnbv q p φ hq hp hφ.le hroot
    Wq Wqp hWq hWqp x hx⟩
