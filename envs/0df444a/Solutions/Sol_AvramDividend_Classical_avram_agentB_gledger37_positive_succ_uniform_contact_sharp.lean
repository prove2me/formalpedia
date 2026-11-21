-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_gledger37_positive_succ_uniform_contact_sharp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T09:46:01.409414+00:00
-- url     : https://prove2.me/submissions/9563f6b2-bb9d-4831-b70c-7bbaf3e27200

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_agentB_topcap_positive_clock_contact_sharp_nnstrip
import Theorems.Thm_AvramDividend_Classical_avram_gledger111_subclock_le_ruin_and_horizon
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- Every positive multi-cell original uniform physical mesh specialises
the sharp stopped positive-clock source after the exact index shift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Contact : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      (w (x - rightLimit D 0 ω) - w x) +
        Finset.sum (Finset.range (m + 1)) (fun i =>
          E (v (i + 1)) *
            ((w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
              (w (Y (v (i + 1))) - w (riskProcess X x D (v (i + 1)) ω)))) +
        E (ρ ω) * (w (riskProcess X x D (ρ ω) ω) - w (Y (ρ ω))) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      q * (Δ : ℝ) * (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω - Δ : ℝ≥0) : ℝ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    ∀ k : ℕ, ∀ᵐ ω ∂P, 0 < ρ ω → max (Contact (k + 1) ω) (0 : ℝ) ≤ B (k + 1) ω := by
  intro Contact B k
  filter_upwards [hprefix] with ω hp hpos
  have hclock : ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := by
    simpa [hτeq ω] using hρle ω
  obtain ⟨hρn, hρruin⟩ :=
    avram_gledger111_subclock_le_ruin_and_horizon
      (ruinTime X x D ω) (n : ℝ≥0) (ρ ω) hclock
  have hs := avram_agentB_topcap_positive_clock_contact_sharp_nnstrip
    X q hq w C hC hTopCap hw0 hw_cont hw_neg hw_grad
    x hx hxc D hD hjump ω n (ρ ω) hpos hρn hρruin j hp k
  have hden : ((k + 1 : ℕ) : ℝ≥0) + 1 = (k : ℝ≥0) + 2 := by
    push_cast
    ring
  have hidx : (k + 1 : ℕ) + 1 = k + 2 := by omega
  have hden' : (k : ℝ≥0) + 1 + 1 = (k : ℝ≥0) + 2 := by ring
  convert hs using 1
  · simpa only [Contact, Nat.cast_add, Nat.cast_one, hden', hidx]
  · simp only [B, Nat.cast_add, Nat.cast_one, hden',
      NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    have hreal : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
    rw [hreal]
