-- Prove2me | solution 1 for AvramDividend.Classical.chat03_ennreal_measurable_of_finite_strict_sublevels
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T07:14:41.53632+00:00
-- url     : https://prove2.me/submissions/623b5a99-26f5-413e-925d-7c95dc88a51f

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-!
Finite-threshold strict sublevel measurability suffices for a
fully measurable ENNReal-valued clock. Its top sublevel is a
countable union of finite natural-horizon sublevel events.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (f : Ω → ℝ≥0∞)
    (h : ∀ t : ℝ≥0,
      MeasurableSet {ω : Ω | f ω < (t : ℝ≥0∞)}) :
    Measurable f := by
  apply measurable_of_Iio
  have hAll : ∀ a : ℝ≥0∞,
      MeasurableSet (f ⁻¹' Set.Iio a) := by
    rw [ENNReal.forall_ennreal]
    constructor
    · intro t
      change MeasurableSet {ω : Ω | f ω < (t : ℝ≥0∞)}
      exact h t
    · have hEach : ∀ n : ℕ,
          MeasurableSet {ω : Ω | f ω < (n : ℝ≥0∞)} := by
        intro n
        simpa using h (n : ℝ≥0)
      have hN : MeasurableSet
          {ω : Ω | ∃ n : ℕ, f ω < (n : ℝ≥0∞)} := by
        simpa only [Set.iUnion_setOf] using
          (MeasurableSet.iUnion hEach)
      have hEq :
          {ω : Ω | f ω < (∞ : ℝ≥0∞)} =
          {ω : Ω | ∃ n : ℕ, f ω < (n : ℝ≥0∞)} := by
        ext ω
        constructor
        · intro hf
          exact ENNReal.exists_nat_gt (ne_top_of_lt hf)
        · rintro ⟨n, hn⟩
          exact lt_of_lt_of_le hn le_top
      change MeasurableSet {ω : Ω | f ω < (∞ : ℝ≥0∞)}
      rw [hEq]
      exact hN
  exact hAll

