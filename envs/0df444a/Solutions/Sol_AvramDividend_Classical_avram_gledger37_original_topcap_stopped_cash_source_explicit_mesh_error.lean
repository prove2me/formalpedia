-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger37_original_topcap_stopped_cash_source_explicit_mesh_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:10:23.510865+00:00
-- url     : https://prove2.me/submissions/be674506-23ce-4221-939c-db4ae42374c1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_agentB_gledger37_original_zero_stopped_clock_budget
import Theorems.Thm_AvramDividend_Classical_avram_agentB_gledger37_positive_mesh_residual_contact_identity
import Theorems.Thm_AvramDividend_Classical_avram_agentB_gledger37_positive_uniform_contact_sharp
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- Original exact stopped cash source: the proved positive contact upper
plus the exact telescope and the zero-clock identity. -/
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
    let H : Ω → ℝ := fun ω =>
      if ρ ω = 0 then w x else
        Real.exp (-(q * (ρ ω : ℝ))) *
          w (riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
    let S : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))))
    ∀ m : ℕ, ∀ᵐ ω ∂P,
      max (H ω - w x - S m ω) (0 : ℝ) ≤
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let u : ℝ≥0 := ρ ω - Δ
        q * (Δ : ℝ) *
          (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo (u : ℝ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by
  intro H S m
  have hB := avram_agentB_gledger37_positive_uniform_contact_sharp
    X hX q hq w C hC hTopCap hw0 hw_cont hw_neg hw_grad
    x hx hxc D hD hjump n hn τ hτeq ρ hρstop hρle j hprefix m
  filter_upwards [hB] with ω hb
  by_cases hz : ρ ω = 0
  · have hzero := avram_agentB_gledger37_original_zero_stopped_clock_budget
      X hX q hq w C hC hTopCap hw0 hw_cont hw_neg hw_grad
      x hx hxc D hD hjump n hn τ hτeq ρ hρstop hρle j hprefix m ω hz
    rw [hzero]
    simp [hz]
  · have hr := avram_agentB_gledger37_positive_mesh_residual_contact_identity
      X hX q hq w C hC hTopCap hw0 hw_cont hw_neg hw_grad
      x hx hxc D hD hjump n hn τ hτeq ρ hρstop hρle j hprefix m ω
      (pos_iff_ne_zero.mpr hz)
    rw [hr]
    exact hb (pos_iff_ne_zero.mpr hz)
