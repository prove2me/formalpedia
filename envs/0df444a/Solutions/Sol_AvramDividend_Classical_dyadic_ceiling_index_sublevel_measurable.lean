-- Prove2me | solution 1 for AvramDividend.Classical.dyadic_ceiling_index_sublevel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:07:23.007894+00:00
-- url     : https://prove2.me/submissions/9b501c22-68af-482d-a2c6-ebcf039f5379

import Mathlib.Probability.Process.Stopping
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal

/-- A dyadic ceiling-index sublevel is known at its corresponding grid time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (n k : ℕ) :
    MeasurableSet[𝓕 ((k : ℝ≥0) / (2 : ℝ≥0) ^ n)]
      {ω : Ω | Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) ≤ k} := by
  let s : ℝ≥0 := (k : ℝ≥0) / (2 : ℝ≥0) ^ n
  have hs : {ω : Ω | Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) ≤ k} =
      {ω : Ω | (τ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)} := by
    ext ω
    simp only [Set.mem_setOf_eq, WithTop.coe_le_coe, Nat.ceil_le]
    change ((τ ω : ℝ) * (2 : ℝ) ^ n ≤ (k : ℝ)) ↔ τ ω ≤ s
    rw [← NNReal.coe_le_coe]
    simp only [s, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast,
      NNReal.coe_ofNat]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).symm
  rw [hs]
  exact hstop.measurableSet_le s
