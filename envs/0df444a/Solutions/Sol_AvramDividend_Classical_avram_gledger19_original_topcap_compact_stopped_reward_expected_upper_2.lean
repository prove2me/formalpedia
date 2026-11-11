-- Prove2me | solution 2 for AvramDividend.Classical.avram_gledger19_original_topcap_compact_stopped_reward_expected_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:53:14.46121+00:00
-- url     : https://prove2.me/submissions/d1bfc650-8ad7-4041-ab5e-145057a4cb2d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger25_original_topcap_postpayment_stopped_positive_residual_vanish
import Theorems.Thm_AvramDividend_Classical_avram_gledger24_original_postpayment_raw_compact_grid_centered
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top14_original_bounded_stop_masked_strict_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_physical_sigma_clock_le_finite_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The postpayment positive-part source error and genuinely centred
    original X,D Gaussian mesh yield the compact expected cash bound. -/
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
    (∫ ω,
       if ρ ω = 0 then w x else
         Real.exp (-(q * (ρ ω : ℝ))) *
           w (riskProcess X x D (ρ ω) ω) +
         (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
           ENNReal.ofReal (Real.exp (-(q * s)))
           ∂(dividendMeasure D ω)).toReal ∂P) ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let H : Ω → ℝ := fun ω =>
    if ρ ω = 0 then w x else
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
  have hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0) := by
    exact avram_f16_original_physical_sigma_clock_le_finite_horizon
      X x D n τ hτeq (fun _ => ρ)
        (by intro k ω; exact hρle ω) 0
  have hHI : Integrable H P := by
    exact avram_ubv_gauss_top14_original_bounded_stop_masked_strict_reward_L1
      X hX hBV hNuZero q hq w C hC hTopCap
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x D hD ρ hρstop (n : ℝ≥0) hρbound
  change (∫ ω, H ω ∂P) ≤ w x
  by_contra hnot
  have hgap : 0 < (∫ ω, H ω ∂P) - w x :=
    sub_pos.mpr (lt_of_not_ge hnot)
  have hε : 0 < ((∫ ω, H ω ∂P) - w x) / 2 := by linarith
  obtain ⟨m, hm, hPlus⟩ :=
    avram_gledger25_original_topcap_postpayment_stopped_positive_residual_vanish
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix _ hε
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
  have hMI : Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by
    simpa only [M, Δ] using
      (avram_gledger24_original_postpayment_raw_compact_grid_centered
        X hBV hNuZero q (le_of_lt hq) w C hTopCap hw_smooth
        x hx D hD.1.1 ρ hρstop j n m hprefix)
  have hPlus' :
      (∫ ω, max (H ω - w x - M ω) (0 : ℝ) ∂P) ≤
        ((∫ ω, H ω ∂P) - w x) / 2 := by
    simpa only [M, Δ, H] using hPlus
  have hSubI : Integrable (fun ω => H ω - w x) P :=
    hHI.sub (integrable_const _)
  have hRI : Integrable (fun ω => H ω - w x - M ω) P :=
    hSubI.sub hMI.1
  have hMaxEq : ∀ ω,
      max (H ω - w x - M ω) (0 : ℝ) =
        ((H ω - w x - M ω) + |H ω - w x - M ω|) / 2 := by
    intro ω
    by_cases hz : 0 ≤ H ω - w x - M ω
    · rw [max_eq_left hz, abs_of_nonneg hz]
      ring
    · have hle : H ω - w x - M ω ≤ 0 := le_of_lt (lt_of_not_ge hz)
      rw [max_eq_right hle, abs_of_nonpos hle]
      ring
  have hPI : Integrable (fun ω => max (H ω - w x - M ω) (0 : ℝ)) P := by
    have hQI : Integrable
        (fun ω => ((H ω - w x - M ω) + |H ω - w x - M ω|) / 2) P :=
      (hRI.add hRI.abs).div_const 2
    have hFunEq :
        (fun ω => max (H ω - w x - M ω) (0 : ℝ)) =
        (fun ω => ((H ω - w x - M ω) + |H ω - w x - M ω|) / 2) :=
      funext hMaxEq
    rw [hFunEq]
    exact hQI
  have hLe :
      (∫ ω, H ω - w x - M ω ∂P) ≤
        (∫ ω, max (H ω - w x - M ω) (0 : ℝ) ∂P) := by
    exact integral_mono hRI hPI (fun ω => le_max_left _ _)
  have hEq :
      (∫ ω, H ω - w x - M ω ∂P) =
        (∫ ω, H ω ∂P) - w x := by
    calc
      (∫ ω, H ω - w x - M ω ∂P) =
          (∫ ω, H ω - w x ∂P) - (∫ ω, M ω ∂P) :=
        integral_sub hSubI hMI.1
      _ = (∫ ω, H ω ∂P) - w x := by
        rw [integral_sub hHI (integrable_const _), hMI.2]
        simp
  linarith
