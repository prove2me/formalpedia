-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_grid_binary_cover_ae_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:23:53.787993+00:00
-- url     : https://prove2.me/submissions/f4ab573f-9f76-4693-87d2-26582c2cc8ad

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Almost surely, every actual bounded-variation Lévy grid increment is
either strictly below the physical drift increment or exactly equal to it. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ i : ℕ, i < n →
      X.X (t (i + 1)) ω - X.X (t i) ω <
        X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)) ∨
      X.X (t (i + 1)) ω - X.X (t i) ω =
        X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)) := by
  filter_upwards [bv_drift_deficit_ae_monotone_all_times X hBV] with ω hMono
  intro i hi
  have horder : t i ≤ t (i + 1) := ht (Nat.le_succ i)
  have hD := hMono horder
  have hco :
      ((t (i + 1) : ℝ) * X.drift - X.X (t (i + 1)) ω) -
        ((t i : ℝ) * X.drift - X.X (t i) ω) =
      (((t (i + 1) - t i : ℝ≥0) : ℝ)) * X.drift -
        (X.X (t (i + 1)) ω - X.X (t i) ω) := by
    rw [NNReal.coe_sub horder]
    ring
  have hnonneg : 0 ≤
      X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)) -
        (X.X (t (i + 1)) ω - X.X (t i) ω) := by
    dsimp at hD
    nlinarith [hco]
  rcases lt_or_eq_of_le hnonneg with hp | hz
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)
