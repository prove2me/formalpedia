-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_stopped_L1_L2_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:04:53.087142+00:00
-- url     : https://prove2.me/submissions/1b86651c-be78-41cf-bc01-dbc3a808ac0a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_stopped_source_L1_L2_jump_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine source-P finite-horizon stopped nonlinear L1 drift and L2
quadratic energies converge ordinarily to zero on shrinking negative marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ f : (ℝ≥0 × Ω) → ℝ≥0∞,
        Measurable[𝓕.rightCont.predictable] f →
        (∫⁻ p, f p ∂μ) =
          (∫⁻ p, f p ∂((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P))) ∧
      let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        (if Y p.1 ∈ Icc (u + δ) v then
          w (Y p.1 + p.2) - w (Y p.1) else 0) -
        (if -1 < p.2 then
          p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
          else 0)
      let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
      ∃ r : ℝ, 0 < r ∧
        ∀ (B : ℕ → Set ℝ)
          (hBm : ∀ n, MeasurableSet (B n))
          (hBnear : ∀ n, B n ⊆ Ioo (-r) 0)
          (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅),
        Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ)
          atTop (𝓝 0) ∧
        Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ)
          atTop (𝓝 0) := by
  obtain ⟨μ, hμ, hprod, hrest⟩ :=
    avram_wave5_03b_actual_finite_horizon_stopped_source_L1_L2_jump_tail
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv T
  refine ⟨μ, hμ, hprod, ?_⟩
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then
      p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
      else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  have hrest' : ∃ r : ℝ, 0 < r ∧
        ∀ (B : ℕ → Set ℝ)
          (hBm : ∀ n, MeasurableSet (B n))
          (hBnear : ∀ n, B n ⊆ Ioo (-r) 0)
          (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅),
        (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) = 0 ∧
        (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ) = 0 :=
    hrest
  obtain ⟨r, hr, hboth⟩ := hrest'
  change ∃ r : ℝ, 0 < r ∧
        ∀ (B : ℕ → Set ℝ)
          (hBm : ∀ n, MeasurableSet (B n))
          (hBnear : ∀ n, B n ⊆ Ioo (-r) 0)
          (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅),
        Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ)
          atTop (𝓝 0) ∧
        Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ)
          atTop (𝓝 0)
  refine ⟨r, hr, ?_⟩
  intro B hBm hBnear hBanti hBempty
  obtain ⟨hL1, hL2⟩ := hboth B hBm hBnear hBanti hBempty
  let A1 (n : ℕ) : ℝ≥0∞ :=
    ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ
  let A2 (n : ℕ) : ℝ≥0∞ :=
    ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ
  have hA1 : Antitone A1 := by
    intro i j hij
    apply lintegral_mono
    intro p
    exact lintegral_mono_set (hBanti hij)
  have hA2 : Antitone A2 := by
    intro i j hij
    apply lintegral_mono
    intro p
    exact lintegral_mono_set (hBanti hij)
  have hZero1 : (⨅ n : ℕ, A1 n) = 0 := hL1
  have hZero2 : (⨅ n : ℕ, A2 n) = 0 := hL2
  have hConv1 : Tendsto A1 atTop (𝓝 0) := by
    have h := tendsto_atTop_iInf hA1
    rw [hZero1] at h
    exact h
  have hConv2 : Tendsto A2 atTop (𝓝 0) := by
    have h := tendsto_atTop_iInf hA2
    rw [hZero2] at h
    exact h
  exact ⟨hConv1, hConv2⟩
