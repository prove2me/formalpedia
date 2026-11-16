-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54b_original_finitegrid_capstrip_positive_error_L1_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:47:46.73117+00:00
-- url     : https://prove2.me/submissions/de4a9706-f045-4b82-b420-59ce005fa3d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_gfinite42_original_compact_diagonal_gaussian_grid_centered
import Theorems.Thm_AvramDividend_Classical_avram_gb26_original_finitecap_strip_event_integrable
import Theorems.Thm_AvramDividend_Classical_avram_gb20_original_finitecap_postpaid_grid_L1_limit
import Theorems.Thm_AvramDividend_Classical_avram_gbB54c_original_finitecap_limit_stopped_cash_source_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
    ∀ (j : ℕ),
      let M : ℕ → Ω → ℝ := fun m ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
        let Z : ℕ → Ω → ℝ := fun i η =>
          X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then deriv w (Y i η) else 1) else 0
        let H : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0) else 0
        (Finset.range (m + 1)).sum (fun i =>
          G i ω * Z i ω + H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let F : Ω → ℝ := fun ω =>
        if ρ ω = 0 then w x else Real.exp (-(q * (ρ ω : ℝ))) *
          w (riskProcess X x D (ρ ω) ω) +
          (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * z))) ∂(dividendMeasure D ω)).toReal
      let Occ : Ω → ℝ := fun ω =>
        ∫ t in Ioo (0 : ℝ) (n : ℝ),
          if t < (ρ ω : ℝ) ∧ b < riskProcess X x D (Real.toNNReal t) ω
          then (1 : ℝ) else 0 ∂volume
      Tendsto (fun m => ∫ ω in A, max ((F ω - w x) - M m ω -
          (((w C.toReal - w b) - (C.toReal - b)) + max X.c 0 * Occ ω)) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k ρ hρstop hρle δ hδ hFloor A hA j M b F Occ
  let K : ℝ := (w C.toReal - w b) - (C.toReal - b)
  let R : ℕ → Ω → ℝ := fun m ω => (F ω - w x) - M m ω - (K + max X.c 0 * Occ ω)
  have hτbound (ω) : τ ω ≤ (n : ℝ≥0) := by
    rw [hτeq ω]; exact (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).2.1 ω
  have hρbound (ω) : ρ ω ≤ (n : ℝ≥0) := (hρle ω).trans ((hσle k ω).trans (hτbound ω))
  have hF : Integrable F P := by simpa only [F] using (avram_gfinite28_original_bounded_stop_masked_strict_reward_L1 X x C hFiniteCap hxc D hD w hw_cont hw_neg q hq ρ hρstop n hρbound)
  have hM (m : ℕ) : IntegrableOn (M m) A P := by
    let N : ℕ → ℕ := fun _ => m
    simpa only [M, N] using (avram_gfinite42_original_compact_diagonal_gaussian_grid_centered
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop hσle
        k ρ hρstop hρle δ hδ hFloor A hA N).1 j
  have hOcc : IntegrableOn Occ A P := by
    simpa only [Occ, b] using (avram_gb26_original_finitecap_strip_event_integrable X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop hσle
      k ρ hρstop hρle δ hδ hFloor A hA j).1
  have hCost : IntegrableOn (fun ω => K + max X.c 0 * Occ ω) A P := (integrable_const (μ := P.restrict A) K).add (hOcc.const_mul (max X.c 0))
  have hR (m : ℕ) : IntegrableOn (R m) A P := ((hF.integrableOn.sub integrableOn_const).sub (hM m)).sub hCost
  have hPos (m : ℕ) : IntegrableOn (fun ω => max (R m ω) 0) A P :=
    ⟨by simpa only [posPart_def] using (hR m).1.posPart, (hR m).2.max_zero⟩
  obtain ⟨N, hNI, hNmean, hNlim⟩ := avram_gb20_original_finitecap_postpaid_grid_L1_limit
    X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop hσle
    k ρ hρstop hρle δ hδ hFloor A hA j
  have hBudget : ∀ᵐ ω ∂(P.restrict A), F ω - w x ≤ N ω + (K + max X.c 0 * Occ ω) := by
    simpa only [F, M, Occ, b, K] using
      (avram_gbB54c_original_finitecap_limit_stopped_cash_source_budget
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
        x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop hσle
        k ρ hρstop hρle δ hδ hFloor A hA j N hNI hNlim)
  have hAbs (m : ℕ) : IntegrableOn (fun ω => |N ω - M m ω|) A P := (hNI.integrableOn.sub (hM m)).abs
  have hUpper (m : ℕ) : (∫ ω in A, max (R m ω) 0 ∂P) ≤ (∫ ω in A, |N ω - M m ω| ∂P) := by
    apply integral_mono_ae (hPos m) (hAbs m)
    filter_upwards [hBudget] with ω hω
    exact max_le (by dsimp only [R, K]; linarith [le_abs_self (N ω - M m ω)])
      (abs_nonneg _)
  have hLower (m : ℕ) : 0 ≤ ∫ ω in A, max (R m ω) 0 ∂P := integral_nonneg (fun ω => le_max_right (R m ω) 0)
  change Tendsto (fun m => ∫ ω in A, max (R m ω) 0 ∂P) atTop (𝓝 (0 : ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hNlim hLower hUpper
