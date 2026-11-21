-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_original_clipped_telescope_cash_residual_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:20:33.85381+00:00
-- url     : https://prove2.me/submissions/eac8a37d-ee74-4c17-a451-136bf0ed1787

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger35_original_clipped_uniform_four_event_telescope
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- A source-exact pathwise stopped cash and postpayment contact identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (n m : ℕ) (ρ : Ω → ℝ≥0)
    (hρruin : ∀ η, (ρ η : ℝ≥0∞) ≤ ruinTime X x D η)
    (hρbound : ∀ η, ρ η ≤ (n : ℝ≥0))
    (ω : Ω) (hpos : 0 < ρ ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let S : ℝ := Finset.sum (Finset.range (m + 1)) (fun i =>
      (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
        E (v (i + 1)) * (w (Z i) - w (Y (v i))))
    let K : ℝ := (w (x - rightLimit D 0 ω) - w x) +
      Finset.sum (Finset.range (m + 1)) (fun i =>
        E (v (i + 1)) *
          ((w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
            (w (Y (v (i + 1))) - w (riskProcess X x D (v (i + 1)) ω)))) +
      E (ρ ω) * (w (riskProcess X x D (ρ ω) ω) - w (Y (ρ ω)))
    let F : ℝ := (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    (if ρ ω = 0 then w x else E (ρ ω) *
      w (riskProcess X x D (ρ ω) ω) + F) - w x - S = K + F := by
  intro Δ v E Y Z S K F
  let A : ℕ → ℝ := fun i => (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
    E (v (i + 1)) * (w (Z i) - w (Y (v i)))
  let Q : ℕ → ℝ := fun i => E (v (i + 1)) *
    ((w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
      (w (Y (v (i + 1))) - w (riskProcess X x D (v (i + 1)) ω)))
  have hTel := avram_gledger35_original_clipped_uniform_four_event_telescope
    X x q D hD w n m ρ hρruin hρbound ω
  have hFour :
      (Finset.range (m + 1)).sum (fun i =>
        (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
        E (v (i + 1)) * (w (Z i) - w (Y (v i))) +
        E (v (i + 1)) * (w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
        E (v (i + 1)) * (w (Y (v (i + 1))) -
          w (riskProcess X x D (v (i + 1)) ω))) =
      (∑ i ∈ Finset.range (m + 1), (A i + Q i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [A, Q]
    ring
  have hS : (∑ i ∈ Finset.range (m + 1), A i) = S := rfl
  have hK : K = (w (x - rightLimit D 0 ω) - w x) +
      (∑ i ∈ Finset.range (m + 1), Q i) +
      E (ρ ω) * (w (riskProcess X x D (ρ ω) ω) - w (Y (ρ ω))) := rfl
  have hTel' : E (ρ ω) * w (riskProcess X x D (ρ ω) ω) =
      w x + K + S := by
    dsimp only at hTel
    rw [hFour, Finset.sum_add_distrib, hS] at hTel
    rw [hK]
    linarith [hTel]
  rw [if_neg (ne_of_gt hpos)]
  linarith [hTel']
