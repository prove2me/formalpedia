-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_true_original_existential_spatial_C2_and_threechannel_mark_L1L2_localisation_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:52:41.763955+00:00
-- url     : https://prove2.me/submissions/013ab630-91d0-41f6-afcf-c85125a052b2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward80a_finitecap_compact_band_cutoff_exists
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_true_original_joint_cap_spatial_and_smallmark_three_tail_budget
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
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (T : ℝ≥0)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (hBV : ¬ X.BoundedVariation)
    (Ccap : ℝ≥0∞) (hCcap : 0 < Ccap)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Ccap})
    (hCfinite : Ccap ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ Ccap)
    (hDcap : IsAdmissibleLe X x Ccap D)
    (N : ℕ) (hN : 0 < N)
    (μsp : Measure (ℝ≥0 × Ω)) [IsFiniteMeasure μsp] :
    ∀ ε : ℝ, 0 < ε →
      ∃ Cband u v δ η : ℝ,
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
        0 < u ∧ 0 < δ ∧ δ ≤ 1 ∧ u + δ < v ∧
        0 < η ∧ η < 1 ∧ v < Cband ∧ v < Ccap.toReal ∧
        ContDiffOn ℝ 2 w (Ioo 0 Cband) ∧
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
  intro ε hε
  obtain ⟨Cband, u, v, δ, η, hu, hδ, hδone, huv,
      hη, hηone, hv, hvCap, hwband⟩ :=
    avram_pj_reward80a_finitecap_compact_band_cutoff_exists
      Ccap hCcap hCfinite w hw_smooth
  refine ⟨Cband, u, v, δ, η, ?_⟩
  dsimp only
  refine ⟨hu, hδ, hδone, huv, hη, hηone, hv, hvCap, hwband, ?_⟩
  exact
    avram_pj_workerC_true_original_joint_cap_spatial_and_smallmark_three_tail_budget
      X x D hD w Cband u v δ hwband hw_cont hw_neg
      hu hδ hδone huv hv μ hμ T B hBm hBneg hBanti hBempty
      hBV Ccap hCcap hCfinite hxc hDcap N hN μsp ε hε
