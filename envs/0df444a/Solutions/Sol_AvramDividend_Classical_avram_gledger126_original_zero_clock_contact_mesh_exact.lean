-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger126_original_zero_clock_contact_mesh_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:28:32.636253+00:00
-- url     : https://prove2.me/submissions/e38545da-1a91-48a7-814b-b77a213680fa

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At zero stop the original finite contact mesh collapses exactly. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (ω : Ω) (q : ℝ) (Δ : ℝ≥0) (N : ℕ) :
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) 0
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℕ → ℝ := fun i => x + X.X (v i) ω - rightLimit D (v i) ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    (w (x - rightLimit D 0 ω) - w x) +
      (∑ i ∈ Finset.range N, E (v (i + 1)) *
        ((w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
         (w (Y (i + 1)) - w (riskProcess X x D (v (i + 1)) ω)))) +
      E 0 * (w (riskProcess X x D 0 ω) -
        w (x + X.X 0 ω - rightLimit D 0 ω)) = 0 := by
  have hD0 : D 0 ω = 0 := hD.1.1.1 ω
  have hX0 : X.X 0 ω = 0 := X.X_zero ω
  have hv : ∀ i : ℕ, min ((i : ℝ≥0) * Δ) 0 = 0 := by
    intro i
    exact min_eq_right (by positivity)
  dsimp
  simp [hv, riskProcess, hD0, hX0] <;> ring
