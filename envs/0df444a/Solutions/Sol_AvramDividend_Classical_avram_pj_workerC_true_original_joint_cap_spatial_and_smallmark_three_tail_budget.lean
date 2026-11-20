-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_true_original_joint_cap_spatial_and_smallmark_three_tail_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:36:21.163197+00:00
-- url     : https://prove2.me/submissions/6d11188c-721d-4144-9eba-7e509b25a022

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_finitecap_both_spatial_boundary_occupations_arbitrarily_small
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_three_tail_source_common_cutoff_epsilon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (T : ℝ≥0)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (hBV : ¬ X.BoundedVariation)
    (Ccap : ℝ≥0∞) (hCcap : 0 < Ccap)
    (hCfinite : Ccap ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ Ccap)
    (hDcap : IsAdmissibleLe X x Ccap D)
    (N : ℕ) (hN : 0 < N)
    (μsp : Measure (ℝ≥0 × Ω)) [IsFiniteMeasure μsp] :
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
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∀ ε : ℝ, 0 < ε →
      ∃ k j n : ℕ,
        μsp {p : ℝ≥0 × Ω |
          0 < riskProcess X x D p.1 p.2 ∧
          riskProcess X x D p.1 p.2 ≤
            (1 : ℝ) / ((k : ℝ) + 1)} ≤ ENNReal.ofReal ε ∧
        (∫ ω, ∫ t in Ioo (0 : ℝ) (N : ℝ),
          if Ccap.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) <
            riskProcess X x D (Real.toNNReal t) ω
          then (1 : ℝ) else 0 ∂volume ∂P) ≤ ε ∧
        (∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) <
            ENNReal.ofReal ε ∧
        (∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ) <
            ENNReal.ofReal ε ∧
        (∫⁻ p : ℝ≥0 × Ω,
          ‖(∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) -
            (∫ z in Iio (0 : ℝ) \ B n, JG (p,z) ∂X.ν)‖ₑ
          ∂(((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) <
            ENNReal.ofReal ε := by
  dsimp only
  intro ε hε
  obtain ⟨k, j, hk, hj⟩ :=
    avram_pj_workerC_original_finitecap_both_spatial_boundary_occupations_arbitrarily_small
      X hBV x Ccap hCcap hCfinite hxc D hDcap N hN μsp ε hε
  obtain ⟨r, hr1, hr2, hr3⟩ :=
    avram_pj_workerC_actual_three_tail_source_common_cutoff_epsilon
      X x D hD w C u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv μ hμ T B hBm hBneg hBanti hBempty ε hε
  exact ⟨k, j, r, hk, hj, hr1, hr2, hr3⟩
