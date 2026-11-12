-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger78_original_topcap_stopped_cash_source_residual_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:37:54.383115+00:00
-- url     : https://prove2.me/submissions/4735db60-a481-4fe2-a475-716cf056b3a1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger77_original_topcap_stopped_cash_source_pointwise_residual
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gledger109_original_stopped_grid_gaussian_source_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gfinite27_original_strict_stopped_rewards_global_meas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option maxHeartbeats 8000000 in

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
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let H : Ω → ℝ := fun ω =>
      if ρ ω = 0 then w x else
        Real.exp (-(q * (ρ ω : ℝ))) * w (riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
    let S : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))))
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
      let F : ℝ := (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
      let T : ℝ := (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ ω : ℝ) - Δ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
      q * Δ * Real.exp (q * (n : ℝ)) * F + T
    ∀ m : ℕ,
      Integrable (fun ω => max (H ω - w x - S (m + 1) ω) (0 : ℝ)) P := by
  intro H S B m
  have hρbound (ω : Ω) : ρ ω ≤ (n : ℝ≥0) := by
    apply (hρle ω).trans
    rw [hτeq ω]
    exact ENNReal.toNNReal_mono (by simp) (min_le_right _ _)
  let δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
  let F : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let T : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
      Ioo ((ρ ω : ℝ) - δ) (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  have hρmeas : Measurable (fun ω : Ω => (ρ ω : ℝ)) := avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable ρ hρstop
  have hF : Integrable F P := by
    obtain ⟨_, hStrict, _⟩ :=
      avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope
        X x C D hD q (le_of_lt hq) (n : ℝ≥0) (fun _ => ρ)
        (by intro k; exact hρmeas) (by intro k ω; exact hρbound ω)
    exact hStrict 0
  have hT : Integrable T P :=
    avram_p3_grid3_original_random_strict_contact_tail_real_integrable
      X x C D hD q (le_of_lt hq) (n : ℝ≥0)
      (fun ω => (ρ ω : ℝ)) hρmeas (by intro ω; positivity)
      (by intro ω; exact_mod_cast hρbound ω) δ
  have hBI : Integrable (B m) P := by
    change Integrable (fun ω => (q * δ * Real.exp (q * (n : ℝ))) * F ω + T ω) P
    exact (hF.const_mul (q * δ * Real.exp (q * (n : ℝ)))).add hT
  have hPath : ∀ᵐ ω ∂P,
      max (H ω - w x - S (m + 1) ω) (0 : ℝ) ≤ B m ω :=
    avram_gledger77_original_topcap_stopped_cash_source_pointwise_residual
      X hX q hq w C hC hTopCap hw0 hw_cont hw_neg hw_grad
      x hx hxc D hD hjump n hn τ hτeq ρ hρstop hρle j hprefix m
  have hH : Measurable H := by
    have hs := avram_gfinite27_original_strict_stopped_rewards_global_meas
      X q w hw_cont hw_neg x C D hD
      ρ hρstop (fun _ : ℕ => ρ) (fun _ => hρstop)
    exact hs.1 0
  have hS (r : ℕ) : Measurable (S r) := by
    exact avram_gledger109_original_stopped_grid_gaussian_source_measurable
      X hX q w hw_cont hw_neg x C D hD n ρ hρstop r
  have hR : Measurable (fun ω =>
      max (H ω - w x - S (m + 1) ω) (0 : ℝ)) :=
    ((hH.sub measurable_const).sub (hS (m + 1))).max measurable_const
  apply hBI.mono' hR.aestronglyMeasurable
  filter_upwards [hPath] with ω hω
  have hNonneg : 0 ≤ max (H ω - w x - S (m + 1) ω) (0 : ℝ) :=
    le_max_right _ _
  have hBnonneg : 0 ≤ B m ω := hNonneg.trans hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg hNonneg,
    abs_of_nonneg hBnonneg] using hω
