-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_killed_resolvent_action_from_qscale_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:52:57.665146+00:00
-- url     : https://prove2.me/submissions/627f604d-4782-43aa-a5b4-753d15914f2b

import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_exists_at_positive_discount_shift_ws01a
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_resolvent_action_without_integrability_assumptions
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Construct both the shifted scale and its genuine analytic killed-kernel action from Wq alone. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (Wq : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq) (p : ℝ) (hp : 0 < p) :
    ∃ Wqp : ℝ → ℝ, ∃ θ : ℝ,
      IsScaleFunction X (q + p) Wqp ∧ 0 < θ ∧ X.ψ θ = q + p ∧
      ∀ x : ℝ, 0 < x →
        (∫ y in Ioi (0 : ℝ),
          Wq y * (Real.exp (-(θ * y)) * Wqp x - Wqp (x - y))) =
          Wq x / p := by
  obtain ⟨Wqp, hWqp⟩ :=
    chat04_unbounded_scale_exists_at_positive_discount_shift_ws01a
      X hnbv q hq Wq hWq p hp
  obtain ⟨θ, hθ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation
      X hnbv (q + p) (add_pos hq hp)
  refine ⟨Wqp, θ, hWqp, hθ, hroot, ?_⟩
  intro x hx
  exact chat04_killed_scale_resolvent_action_without_integrability_assumptions
    X hnbv q p θ hq hp (le_of_lt hθ) hroot Wq Wqp
    hWq hWqp hWqp.1 x hx
