-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_cap_start_zero_grid_blocks_strict_band_cofinality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:44:12.791423+00:00
-- url     : https://prove2.me/submissions/c8b4e540-d65d-4b4b-9080-ab766efed1e0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A cap-start without initial payout cannot lie in any strictly subcap grid band at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (c x : ℝ) (hc : 0 < c) (hxc : x = c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (hNoInitialPayment : rightLimit D 0 ω = 0)
    (r : ℕ → ℝ≥0) (hr0 : r 0 = 0)
    (lower upper : ℕ → ℝ) (hUpper : ∀ n, upper n < c) :
    ¬ (∀ m : ℕ, ∃ n : ℕ, m < n ∧
      ∀ k ≤ m, lower n ≤ x + X.X (r k) ω - rightLimit D (r k) ω ∧
        x + X.X (r k) ω - rightLimit D (r k) ω ≤ upper n) := by
  have hZ0 : x + X.X (r 0) ω - rightLimit D (r 0) ω = c := by
    calc
      x + X.X (r 0) ω - rightLimit D (r 0) ω = x + 0 - 0 := by
        rw [hr0, X.X_zero ω, hNoInitialPayment]
      _ = c := by simpa using hxc
  intro hCover
  obtain ⟨n, _, hPrefix⟩ := hCover 0
  have hUpperAtZero := (hPrefix 0 (Nat.zero_le 0)).2
  rw [hZ0] at hUpperAtZero
  exact (not_lt_of_ge hUpperAtZero) (hUpper n)
