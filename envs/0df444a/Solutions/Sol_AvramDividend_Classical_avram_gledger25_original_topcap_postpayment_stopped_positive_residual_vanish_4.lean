-- Prove2me | solution 4 for AvramDividend.Classical.avram_gledger25_original_topcap_postpayment_stopped_positive_residual_vanish
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:54:16.306093+00:00
-- url     : https://prove2.me/submissions/1909d00b-6d51-492d-bcbf-9855404bb680
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_gledger32_original_stopping_dividend_cash_vs_clipped_source
import Theorems.Thm_AvramDividend_Classical_avram_gledger28_original_clipped_source_vs_postpayment_gaussian_mesh
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top14_original_bounded_stop_masked_strict_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_gledger24_original_postpayment_raw_compact_grid_centered
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_physical_sigma_clock_le_finite_horizon
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
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
    ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, 0 < m ∧
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let M : Ω → ℝ := fun ω =>
        ∑ i ∈ Finset.range m,
          let s : ℝ≥0 := (i : ℝ≥0) * Δ
          if s < ρ ω then
            let y := x + X.X s ω - rightLimit D s ω
            let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
            Real.exp (-(q * (s : ℝ))) *
              (deriv w y * Z +
                (iteratedDeriv 2 w y / 2) * (Z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
          else 0
      (∫ ω, max (H ω - w x - M ω) (0 : ℝ) ∂P) ≤ ε := by
  letI : IsProbabilityMeasure P := X.isProbability
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
    ∑ i ∈ Finset.range (m + 1),
      ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
        E (v (i + 1)) * (w (Z i) - w (Y (v i))))
  let M : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    ∑ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then
        let y := x + X.X s ω - rightLimit D s ω
        let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        Real.exp (-(q * (s : ℝ))) *
          (deriv w y * z + (iteratedDeriv 2 w y / 2) *
            (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0
  change ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, 0 < m ∧ (∫ ω, max (H ω - w x - M m ω) (0 : ℝ) ∂P) ≤ ε
  intro ε hε
  have he : 0 < ε / 2 := by linarith
  obtain ⟨k₁, hk₁⟩ :=
    avram_gledger32_original_stopping_dividend_cash_vs_clipped_source
      X hX q hq w C hC hTopCap hw0 hw_cont hw_neg hw_grad
      x hx hxc D hD hjump n hn τ hτeq ρ hρstop hρle j hprefix (ε / 2) he
  obtain ⟨k₂, hk₂⟩ :=
    avram_gledger28_original_clipped_source_vs_postpayment_gaussian_mesh
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen
      x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix (ε / 2) he
  let m : ℕ := max k₁ k₂ + 1
  have hm₁ : k₁ ≤ m := by dsimp [m]; omega
  have hm₂ : k₂ ≤ m := by dsimp [m]; omega
  obtain ⟨hAint, hAbound⟩ := hk₁ m hm₁
  obtain ⟨hBint, hBbound⟩ := hk₂ m hm₂
  have hσle : ∀ k ω, (fun _ : ℕ => ρ) k ω ≤ τ ω := by
    intro k ω
    exact hρle ω
  have hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0) :=
    (avram_f16_original_physical_sigma_clock_le_finite_horizon
      X x D n τ hτeq (fun _ : ℕ => ρ) hσle) 0
  have hHint : Integrable H P :=
    avram_ubv_gauss_top14_original_bounded_stop_masked_strict_reward_L1
      X hX hBV hNuZero q hq w C hC hTopCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x D hD ρ hρstop (n : ℝ≥0) hρbound
  have hMint : Integrable (M m) P :=
    (avram_gledger24_original_postpayment_raw_compact_grid_centered
      X hBV hNuZero q (le_of_lt hq) w C hTopCap hw_smooth
      x hx D hD.1.1 ρ hρstop j n m hprefix).1
  have hleft : Integrable
      (fun ω => max (H ω - w x - M m ω) (0 : ℝ)) P := by
    exact ((hHint.sub (integrable_const (w x))).sub hMint).sup
      (integrable_const 0)
  have hpoint (ω : Ω) :
      max (H ω - w x - M m ω) (0 : ℝ) ≤
        max (H ω - w x - S m ω) 0 + max (S m ω - M m ω) 0 := by
    apply max_le
    · have ha := le_max_left (H ω - w x - S m ω) (0 : ℝ)
      have hb := le_max_left (S m ω - M m ω) (0 : ℝ)
      linarith
    · have ha := le_max_right (H ω - w x - S m ω) (0 : ℝ)
      have hb := le_max_right (S m ω - M m ω) (0 : ℝ)
      linarith
  refine ⟨m, by dsimp [m]; omega, ?_⟩
  calc
    (∫ ω, max (H ω - w x - M m ω) (0 : ℝ) ∂P) ≤
        ∫ ω, (max (H ω - w x - S m ω) 0 +
          max (S m ω - M m ω) 0) ∂P :=
      integral_mono hleft (hAint.add hBint) hpoint
    _ = (∫ ω, max (H ω - w x - S m ω) 0 ∂P) +
        (∫ ω, max (S m ω - M m ω) 0 ∂P) :=
      integral_add hAint hBint
    _ ≤ ε / 2 + ε / 2 := add_le_add hAbound hBbound
    _ = ε := by ring
