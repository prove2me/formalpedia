-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_gledger37_positive_uniform_contact_sharp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:31:46.645173+00:00
-- url     : https://prove2.me/submissions/14b85ce0-f32c-4ad7-80e3-eff914503ae3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_agentB_gledger37_positive_single_uniform_contact_sharp
import Theorems.Thm_AvramDividend_Classical_avram_agentB_gledger37_positive_succ_uniform_contact_sharp
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- Union of the proved original single-cell and every multi-cell
sharp positive stopped cash contact estimate. -/
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
    ∀ m : ℕ, ∀ᵐ ω ∂P, 0 < ρ ω → max (Contact m ω) (0 : ℝ) ≤ B m ω := by
  intro Contact B m
  cases m with
  | zero =>
      exact avram_agentB_gledger37_positive_single_uniform_contact_sharp
        X hX q hq w C hC hTopCap hw0 hw_cont hw_neg hw_grad
        x hx hxc D hD hjump n hn τ hτeq ρ hρstop hρle j hprefix
  | succ k =>
      simpa only [Nat.succ_eq_add_one] using
        (avram_agentB_gledger37_positive_succ_uniform_contact_sharp
          X hX q hq w C hC hTopCap hw0 hw_cont hw_neg hw_grad
          x hx hxc D hD hjump n hn τ hτeq ρ hρstop hρle j hprefix k)
