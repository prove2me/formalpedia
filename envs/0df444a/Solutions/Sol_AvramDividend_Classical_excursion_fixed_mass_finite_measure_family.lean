-- Prove2me | solution 1 for AvramDividend.Classical.excursion_fixed_mass_finite_measure_family
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:08:47.736502+00:00
-- url     : https://prove2.me/submissions/f31df954-fcb6-4d4b-9f2a-b0779ac71374

import Mathlib.MeasureTheory.Measure.FiniteMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-!
A sequence of ordinary measures with the same finite ENNReal
total mass can be packaged as a sequence of FiniteMeasure
objects with the corresponding common NNReal mass.
-/
theorem solution
    (β : ℕ → Measure ℝ) (c : NNReal)
    (hmass : ∀ n : ℕ, β n univ = (c : ENNReal)) :
    ∃ ν : ℕ → FiniteMeasure ℝ,
      (∀ n : ℕ, (ν n : Measure ℝ) = β n) ∧
      (∀ n : ℕ, (ν n).mass = c) := by
  have hfinite (n : ℕ) : IsFiniteMeasure (β n) :=
    ⟨by rw [hmass n]; exact ENNReal.coe_lt_top⟩
  let ν : ℕ → FiniteMeasure ℝ := fun n => ⟨β n, hfinite n⟩
  refine ⟨ν, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_mass]
    exact hmass n
