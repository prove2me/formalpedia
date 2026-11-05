-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_full_grid_drift_jump_commutator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:52:29.012294+00:00
-- url     : https://prove2.me/submissions/6b05aed8-5e2a-4e15-8a35-1b6a4bae341f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_negative_raw_jump_grid_caplinear_eq_w

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact original drift-first and raw-negative-jump source identity:
the only difference from the true w kernel is the literal mixed
drift/jump commutator, with no chronological rearrangement. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (u : ℕ → ℝ≥0) (n : ℕ) (hu : Monotone u)
    (hCap : ∀ i : ℕ, i < n →
      C = ⊤ ∨ x + X.X (u i) ω - rightLimit D (u i) ω ≤ C.toReal) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let z : ℕ → ℝ := fun i => x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => ((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift
    let j : ℕ → ℝ := fun i =>
      ∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) v - X.X v ω
      else 0
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    (∑ i ∈ Finset.range n, e i * (V (z i + c i - j i) - V (z i))) =
      (∑ i ∈ Finset.range n, e i * (V (z i + c i) - V (z i))) +
      (∑ i ∈ Finset.range n, e i * (w (z i - j i) - w (z i))) +
      (∑ i ∈ Finset.range n,
        e i * (V (z i + c i - j i) - V (z i + c i) -
          V (z i - j i) + V (z i))) := by
  intro V z c j e
  have hRaw :
      (∑ i ∈ Finset.range n, e i * (V (z i - j i) - V (z i))) =
      (∑ i ∈ Finset.range n, e i * (w (z i - j i) - w (z i))) := by
    simpa only [V, z, j, e] using
      avram_p3_2_original_negative_raw_jump_grid_caplinear_eq_w
        X ω x D w C q u n hu hCap
  calc
    _ = (∑ i ∈ Finset.range n, e i * (V (z i + c i) - V (z i))) +
        (∑ i ∈ Finset.range n, e i * (V (z i - j i) - V (z i))) +
        (∑ i ∈ Finset.range n,
          e i * (V (z i + c i - j i) - V (z i + c i) -
            V (z i - j i) + V (z i))) := by
        simp only [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = _ := by rw [hRaw]
