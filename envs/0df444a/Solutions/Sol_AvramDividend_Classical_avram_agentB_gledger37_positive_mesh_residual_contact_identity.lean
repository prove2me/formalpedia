-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_gledger37_positive_mesh_residual_contact_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:14:46.58437+00:00
-- url     : https://prove2.me/submissions/fdd86c22-7a14-40be-a1cd-075bfc87b8e0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_agentB_original_clipped_telescope_cash_residual_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- The original exact stopped cash residual is precisely the minimal
physical contact telescope, with all surplus hypotheses discharged. -/
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
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨
      (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
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
    let H : Ω → ℝ := fun ω =>
      if ρ ω = 0 then w x else
        Real.exp (-(q * (ρ ω : ℝ))) * w (riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    let S : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))))
    let Contact : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      (w (x - rightLimit D 0 ω) - w x) +
        Finset.sum (Finset.range (m + 1)) (fun i =>
          E (v (i + 1)) * ((w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
              (w (Y (v (i + 1))) - w (riskProcess X x D (v (i + 1)) ω)))) +
        E (ρ ω) * (w (riskProcess X x D (ρ ω) ω) - w (Y (ρ ω))) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    ∀ m : ℕ, ∀ ω : Ω, 0 < ρ ω →
      H ω - w x - S m ω = Contact m ω := by
  intro H S Contact m ω hpos
  have hρbound (η : Ω) : ρ η ≤ (n : ℝ≥0) :=
    (hρle η).trans (by
      rw [hτeq η]
      exact ENNReal.toNNReal_mono (by simp) (min_le_right _ _))
  have hρruin (η : Ω) : (ρ η : ℝ≥0∞) ≤ ruinTime X x D η := by
    calc
      (ρ η : ℝ≥0∞) ≤ (τ η : ℝ≥0∞) := by exact_mod_cast hρle η
      _ = min (ruinTime X x D η) (n : ℝ≥0∞) := by
        rw [hτeq η]; simp [ENNReal.coe_toNNReal]
      _ ≤ ruinTime X x D η := min_le_left _ _
  have hminimal := avram_agentB_original_clipped_telescope_cash_residual_exact
    X x q D hD.1.1 w n m ρ hρruin hρbound ω hpos
  exact hminimal
