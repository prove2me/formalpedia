-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger32_original_stopping_dividend_cash_vs_clipped_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T20:04:23.90782+00:00
-- url     : https://prove2.me/submissions/1dda2508-876d-47a7-9ad0-d5b71c01ea7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger44_original_stopped_pathwise_cash_source_weighted
import Theorems.Thm_AvramDividend_Classical_avram_gledger42_original_strict_discounted_cash_mesh_error_L1
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_physical_sigma_clock_le_finite_horizon
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original stopped cash error is bounded by a proved L1 error. -/
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
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (H ω - w x - S m ω) (0 : ℝ)) P ∧
      (∫ ω, max (H ω - w x - S m ω) (0 : ℝ) ∂P) ≤ ε := by
  let H : Ω → ℝ := fun ω => if ρ ω = 0 then w x else
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
  let B : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
    let F : ℝ :=
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    let T : ℝ :=
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((ρ ω : ℝ) - Δ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    q * Δ * Real.exp (q * (n : ℝ)) * F + T
  change ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
    Integrable (fun ω => max (H ω - w x - S m ω) (0 : ℝ)) P ∧
    (∫ ω, max (H ω - w x - S m ω) (0 : ℝ) ∂P) ≤ ε
  have hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0) :=
    avram_f16_original_physical_sigma_clock_le_finite_horizon
      X x D n τ hτeq (fun _ => ρ) (by intro k ω; exact hρle ω) 0
  have hPath (m : ℕ) :
      Integrable (fun ω => max (H ω - w x - S (m + 1) ω) (0 : ℝ)) P ∧
      (∀ᵐ ω ∂P, max (H ω - w x - S (m + 1) ω) (0 : ℝ) ≤ B m ω) :=
    avram_gledger44_original_stopped_pathwise_cash_source_weighted
      X hX q hq w C hC hTopCap hw0 hw_cont hw_neg hw_grad x hx hxc
      D hD hjump n hn τ hτeq ρ hρstop hρle j hprefix m
  intro ε hε
  obtain ⟨k, hk⟩ := avram_gledger42_original_strict_discounted_cash_mesh_error_L1
    X hX x C D hD q hq n hn ρ hρstop hρbound ε hε
  refine ⟨k + 1, ?_⟩
  intro m hm
  let r := m - 1
  have hmr : r + 1 = m := by dsimp [r]; omega
  have hkr : k ≤ r := by dsimp [r]; omega
  obtain ⟨hPI, hPt⟩ := hPath r
  obtain ⟨hBI, hBle⟩ := hk r hkr
  have hPI' : Integrable (fun ω => max (H ω - w x - S m ω) (0 : ℝ)) P := by
    simpa only [hmr] using hPI
  have hPt' : ∀ᵐ ω ∂P, max (H ω - w x - S m ω) (0 : ℝ) ≤ B r ω := by
    simpa only [hmr] using hPt
  exact ⟨hPI', (integral_mono_ae hPI' hBI hPt').trans hBle⟩
