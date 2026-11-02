-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_actual_original_controlled_four_term_discounted_finite_grid_chain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:14:07.451884+00:00
-- url     : https://prove2.me/submissions/decadc65-6621-4096-91cd-1824a31a0962

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (hzero : u 0 = 0) (n : ℕ) :
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    E (u n) * w (Y (u n)) =
      w x + (w (x - rightLimit D 0 ω) - w x) +
      ∑ i ∈ Finset.range n,
        ((E (u (i + 1)) - E (u i)) * w (Y (u i)) +
          E (u (i + 1)) * (w (Z i) - w (Y (u i))) +
          E (u (i + 1)) *
            (w (riskProcess X x D (u (i + 1)) ω) - w (Z i)) +
          E (u (i + 1)) *
            (w (Y (u (i + 1))) -
              w (riskProcess X x D (u (i + 1)) ω))) := by
  dsimp only
  classical
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let Y : ℝ≥0 → ℝ := fun t =>
    x + X.X t ω - rightLimit D t ω
  let Z : ℕ → ℝ := fun i =>
    x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
  let K : ℕ → ℝ := fun i =>
    ((E (u (i + 1)) - E (u i)) * w (Y (u i)) +
      E (u (i + 1)) * (w (Z i) - w (Y (u i))) +
      E (u (i + 1)) *
        (w (riskProcess X x D (u (i + 1)) ω) - w (Z i)) +
      E (u (i + 1)) *
        (w (Y (u (i + 1))) -
          w (riskProcess X x D (u (i + 1)) ω)))
  have hstep (i : ℕ) :
      K i = E (u (i + 1)) * w (Y (u (i + 1))) -
        E (u i) * w (Y (u i)) := by
    dsimp [K, Y, Z, riskProcess]
    ring
  have htel : ∀ k : ℕ,
      (∑ i ∈ Finset.range k, K i) =
        E (u k) * w (Y (u k)) -
          E (u 0) * w (Y (u 0)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, hstep]
      ring
  have hclock : E (u 0) = 1 := by
    simp [E, hzero]
  have hYzero : Y (u 0) = x - rightLimit D 0 ω := by
    simp [Y, hzero, X.X_zero]
  change E (u n) * w (Y (u n)) =
    w x + (w (x - rightLimit D 0 ω) - w x) +
      ∑ i ∈ Finset.range n, K i
  rw [htel n, hclock, hYzero]
  ring
