-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_topcap_stopped_dividend_contact_sharp_mesh_correction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T09:46:34.001503+00:00
-- url     : https://prove2.me/submissions/1f812904-1449-48a6-a3fb-4a6d45da4611

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger125_original_zero_clock_cash_components_vanish
import Theorems.Thm_AvramDividend_Classical_avram_gledger126_original_zero_clock_contact_mesh_exact
import Theorems.Thm_AvramDividend_Classical_avram_agentB_topcap_positive_clock_contact_sharp_fixed_mesh
import Theorems.Thm_AvramDividend_Classical_avram_gledger111_subclock_le_ruin_and_horizon
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    ∀ m : ℕ,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
      let v : ℕ → Ω → ℝ≥0 := fun i ω =>
        min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v i ω) ω - rightLimit D (v i ω) ω
      let Z : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
      let F : Ω → ℝ := fun ω =>
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let B : Ω → ℝ := fun ω =>
        let δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
        let T : ℝ :=
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
              Ioo ((ρ ω : ℝ) - δ) (ρ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal
        q * δ * (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal + T
      ∀ᵐ ω ∂P,
        max (
          (w (x - rightLimit D 0 ω) - w x) +
          Finset.sum (Finset.range (m + 2)) (fun i =>
            E (v (i + 1) ω) *
              ((w (riskProcess X x D (v (i + 1) ω) ω) - w (Z i ω)) +
                (w (Y (i + 1) ω) -
                  w (riskProcess X x D (v (i + 1) ω) ω)))) +
          E (ρ ω) * (w (riskProcess X x D (ρ ω) ω) -
            w (x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω)) +
          F ω) (0 : ℝ) ≤ B ω := by
  intro m
  let F : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let B : Ω → ℝ := fun ω =>
    let δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
    let T : ℝ :=
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((ρ ω : ℝ) - δ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    q * δ * (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal + T
  filter_upwards [hprefix] with ω hp
  have hclock : ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := by
    simpa [hτeq ω] using hρle ω
  obtain ⟨hρn, hρruin⟩ :=
    avram_gledger111_subclock_le_ruin_and_horizon
      (ruinTime X x D ω) (n : ℝ≥0) (ρ ω) hclock
  by_cases hzero : ρ ω = 0
  · have hcontact :=
      avram_gledger126_original_zero_clock_contact_mesh_exact
        X x C D hD w ω q ((n : ℝ≥0) / ((m : ℝ≥0) + 2)) (m + 2)
    have hcash :=
      avram_gledger125_original_zero_clock_cash_components_vanish
        D ω (ruinTime X x D ω) q
        (((n : ℝ≥0) / ((m : ℝ≥0) + 2)) : ℝ)
    have hmax := max_le (le_of_eq hcontact) (le_refl (0 : ℝ))
    have hFzero : F ω = 0 := by simpa only [F, hzero, NNReal.coe_zero] using hcash.1
    have hBzero : B ω = 0 := by
      simpa [B, hzero, NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_add]
        using hcash.2
    change max (_ + F ω) 0 ≤ B ω
    rw [hFzero, hBzero]
    simpa [hzero] using hmax
  · have hpos : 0 < ρ ω := pos_iff_ne_zero.mpr hzero
    have hpositiveLedger :=
      avram_agentB_topcap_positive_clock_contact_sharp_fixed_mesh
        X q hq w C hC hTopCap hw0 hw_cont hw_neg hw_grad
        x hx hxc D hD hjump ω n (ρ ω)
        hpos hρn hρruin j hp m
    simpa [NNReal.coe_div] using hpositiveLedger
