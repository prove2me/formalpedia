-- Prove2me | solution 3 for AvramDividend.Classical.avram_gledger25_original_topcap_postpayment_stopped_positive_residual_vanish
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:20:13.052674+00:00
-- url     : https://prove2.me/submissions/2f7009ce-f904-47d4-8ac7-486e7dcf0333
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger32_original_stopping_dividend_cash_vs_clipped_source
import Theorems.Thm_AvramDividend_Classical_avram_gledger28_original_clipped_source_vs_postpayment_gaussian_mesh
import Theorems.Thm_AvramDividend_Classical_avram_gledger24_original_postpayment_raw_compact_grid_centered
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top14_original_bounded_stop_masked_strict_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_physical_sigma_clock_le_finite_horizon
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original stopped source accounting with a genuine stopping time. -/
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
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
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
  classical
  letI : IsProbabilityMeasure P := X.isProbability
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
  let M : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    Finset.sum (Finset.range m) (fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then
        let y := x + X.X s ω - rightLimit D s ω
        let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        Real.exp (-(q * (s : ℝ))) * (deriv w y * Z +
          (iteratedDeriv 2 w y / 2) * (Z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0)
  change ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, 0 < m ∧
    (∫ ω, max (H ω - w x - M m ω) (0 : ℝ) ∂P) ≤ ε
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨ka, hka⟩ := avram_gledger32_original_stopping_dividend_cash_vs_clipped_source
    X hX q hq w C hC hTopCap hw0 hw_cont hw_neg hw_grad x hx hxc
    D hD hjump n hn τ hτeq ρ hρstop hρle j hprefix (ε / 2) hhalf
  obtain ⟨kb, hkb⟩ := avram_gledger28_original_clipped_source_vs_postpayment_gaussian_mesh
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth
    hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle
    j hprefix (ε / 2) hhalf
  let m : ℕ := max ka kb + 1
  have hm : 0 < m := Nat.zero_lt_succ _
  obtain ⟨hAI, hAle⟩ := hka m (by omega)
  obtain ⟨hBI, hBle⟩ := hkb m (by omega)
  have hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0) :=
    avram_f16_original_physical_sigma_clock_le_finite_horizon
      X x D n τ hτeq (fun _ => ρ) (by intro k ω; exact hρle ω) 0
  have hHI : Integrable H P :=
    avram_ubv_gauss_top14_original_bounded_stop_masked_strict_reward_L1
      X hX hBV hNuZero q hq w C hC hTopCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x D hD ρ hρstop (n : ℝ≥0) hρbound
  have hMI : Integrable (M m) P := by
    simpa only [M] using
      (avram_gledger24_original_postpayment_raw_compact_grid_centered
        X hBV hNuZero q (le_of_lt hq) w C hTopCap hw_smooth
        x hx D hD.1.1 ρ hρstop j n m hprefix).1
  have hRI : Integrable (fun ω => H ω - w x - M m ω) P :=
    (hHI.sub (integrable_const _)).sub hMI
  have hPI : Integrable (fun ω => max (H ω - w x - M m ω) (0 : ℝ)) P := by
    have hEq : (fun ω => max (H ω - w x - M m ω) (0 : ℝ)) =
        (fun ω => ((H ω - w x - M m ω) + |H ω - w x - M m ω|) / 2) := by
      funext ω
      by_cases hz : 0 ≤ H ω - w x - M m ω
      · rw [max_eq_left hz, abs_of_nonneg hz]; ring
      · have hz' : H ω - w x - M m ω ≤ 0 := le_of_lt (lt_of_not_ge hz)
        rw [max_eq_right hz', abs_of_nonpos hz']; ring
    rw [hEq]
    exact (hRI.add hRI.abs).div_const 2
  have hPt (ω : Ω) :
      max (H ω - w x - M m ω) (0 : ℝ) ≤
        max (H ω - w x - S m ω) 0 + max (S m ω - M m ω) 0 := by
    apply max_le
    · have h₁ := le_max_left (H ω - w x - S m ω) (0 : ℝ)
      have h₂ := le_max_left (S m ω - M m ω) (0 : ℝ)
      linarith
    · have h₁ := le_max_right (H ω - w x - S m ω) (0 : ℝ)
      have h₂ := le_max_right (S m ω - M m ω) (0 : ℝ)
      linarith
  refine ⟨m, hm, ?_⟩
  calc
    (∫ ω, max (H ω - w x - M m ω) (0 : ℝ) ∂P) ≤
        (∫ ω, max (H ω - w x - S m ω) 0 +
          max (S m ω - M m ω) 0 ∂P) :=
      integral_mono hPI (hAI.add hBI) hPt
    _ = (∫ ω, max (H ω - w x - S m ω) 0 ∂P) +
          (∫ ω, max (S m ω - M m ω) 0 ∂P) := integral_add hAI hBI
    _ ≤ ε := by linarith
