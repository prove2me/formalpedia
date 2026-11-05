-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_caplinear_drift_raw_jump_discount_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:28:18.156241+00:00
-- url     : https://prove2.me/submissions/35ef0820-c5a9-4619-972a-db8b5ae4eb2a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact original Lévy cap-linear source split into chronological drift
and negative-jump contributions on every discounted physical grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (u : ℕ → ℝ≥0) (n : ℕ) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let base : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let drift : ℕ → ℝ := fun i =>
      ((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift
    let jump : ℕ → ℝ := fun i =>
      ∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0
    let disc : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    (∑ i ∈ Finset.range n,
      disc i * (V (base i + drift i - jump i) - V (base i))) =
    (∑ i ∈ Finset.range n,
      disc i * (V (base i + drift i) - V (base i))) +
    (∑ i ∈ Finset.range n,
      disc i * (V (base i + drift i - jump i) -
        V (base i + drift i))) := by
  intro V base drift jump disc
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring
