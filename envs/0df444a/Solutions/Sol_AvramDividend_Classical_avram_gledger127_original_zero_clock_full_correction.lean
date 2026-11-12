-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger127_original_zero_clock_full_correction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:55:21.717135+00:00
-- url     : https://prove2.me/submissions/49cb530a-9b8d-4bfa-bd6a-23fc0cfb6d38

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_gledger125_original_zero_clock_cash_components_vanish
import Theorems.Thm_AvramDividend_Classical_avram_gledger126_original_zero_clock_contact_mesh_exact
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original time-zero cash and contact are both exactly exhausted. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (ω : Ω) (q : ℝ) (Δ : ℝ≥0)
    (n N : ℕ) :
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) 0
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℕ → ℝ := fun i => x + X.X (v i) ω - rightLimit D (v i) ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let F : ℝ := (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    let T : ℝ := (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
      Ioo (-(Δ : ℝ)) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    max ((w (x - rightLimit D 0 ω) - w x) +
      (∑ i ∈ Finset.range N, E (v (i + 1)) *
        ((w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
         (w (Y (i + 1)) - w (riskProcess X x D (v (i + 1)) ω)))) +
      E 0 * (w (riskProcess X x D 0 ω) -
        w (x + X.X 0 ω - rightLimit D 0 ω)) + F) 0 ≤
      q * (Δ : ℝ) * Real.exp (q * (n : ℝ)) * F + T := by
  have hcontact := avram_gledger126_original_zero_clock_contact_mesh_exact
    X x C D hD w ω q Δ N
  have hcash := avram_gledger125_original_zero_clock_cash_components_vanish
    D ω (ruinTime X x D ω) q (Δ : ℝ)
  dsimp at hcontact hcash ⊢
  have hmax := max_le (le_of_eq hcontact) (le_refl (0 : ℝ))
  simpa only [hcash.1, hcash.2, add_zero, mul_zero, zero_add] using hmax
