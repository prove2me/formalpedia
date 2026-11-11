-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger35_original_clipped_uniform_four_event_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T19:01:20.75495+00:00
-- url     : https://prove2.me/submissions/0c6b1406-d5c9-44df-852c-f2dcc83dc227

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gauss_ledger14_original_clipped_strict_prepayment_four_event
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Use the original Lévy/dividend trajectory and the exact stopped
    uniform mesh, including the prepayment terminal right-atom ledger. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (n m : ℕ) (ρ : Ω → ℝ≥0)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0)) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    E (ρ ω) * w (riskProcess X x D (ρ ω) ω) =
      w x + (w (x - rightLimit D 0 ω) - w x) +
      (∑ i ∈ Finset.range (m + 1),
        ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))) +
          E (v (i + 1)) *
            (w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
          E (v (i + 1)) *
            (w (Y (v (i + 1))) -
              w (riskProcess X x D (v (i + 1)) ω)))) +
      E (ρ ω) * (w (riskProcess X x D (ρ ω) ω) - w (Y (ρ ω))) := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let u : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  have hu : Monotone u := by
    intro i j hij
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hij
    · positivity
  have hu0 : u 0 = 0 := by simp [u]
  have hden : ((m : ℝ≥0) + 1) ≠ 0 := by positivity
  have huend : u (m + 1) = (n : ℝ≥0) := by
    dsimp [u, Δ]
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  have hcover : ρ ω ≤ u (m + 1) := by
    rw [huend]
    exact hρbound ω
  exact avram_gauss_ledger14_original_clipped_strict_prepayment_four_event
    X x q D hD w ω ρ (hρruin ω) u hu hu0 (m + 1) hcover
