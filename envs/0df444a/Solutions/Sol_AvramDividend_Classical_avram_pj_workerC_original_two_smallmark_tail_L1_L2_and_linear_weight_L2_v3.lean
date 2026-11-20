-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_two_smallmark_tail_L1_L2_and_linear_weight_L2_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:09:20.595251+00:00
-- url     : https://prove2.me/submissions/9d30989c-2dd7-4b47-89a5-491fbffc59da

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_natural_negative_cutoff_predictable_L2_energy_both
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_bounded_predictable_weight_full_negative_C2_source_L1_L2_tendsto_zero
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
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (ρ : ℝ≥0 × Ω → ℝ)
    (hρm : Measurable[𝓕.rightCont.predictable] ρ)
    (hρ : ∀ p, 0 ≤ ρ p ∧ ρ p ≤ 1)
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤) :
    let Bnat : ℕ → Set ℝ := fun n =>
      Ioo (-(1 / ((n : ℝ) + 1))) (0 : ℝ)
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
    (Tendsto (fun n : ℕ => (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
      ({r : ((ℝ≥0 × Ω) × ℝ) | r.2 ∈ Bnat n}).indicator
        (fun r => ENNReal.ofReal ((g r.1 * r.2)^2)) p
      ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
        μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) atTop (𝓝 (0 : ℝ≥0∞)) ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Tendsto (fun n : ℕ =>
        eLpNorm
          (({r : ((ℝ≥0 × Ω) × ℝ) | r.2 ∈ Bnat n}).indicator
            (fun r : ((ℝ≥0 × Ω) × ℝ) => g r.1 * r.2))
          (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))
        atTop (𝓝 (0 : ℝ≥0∞)))) ∧
    (Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal (|ρ p * HS (p,z)|) ∂X.ν ∂μ)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((ρ p * HS (p,z)) ^ 2) ∂X.ν ∂μ)
      atTop (𝓝 0)) := by
  constructor
  · exact avram_jump6_B_original_natural_negative_cutoff_predictable_L2_energy_both
      X μ g hgm hgL2
  · exact avram_wave5_03b_actual_bounded_predictable_weight_full_negative_C2_source_L1_L2_tendsto_zero
      X x D hD w C u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv μ hμ B hBm hBneg hBanti hBempty ρ hρm hρ
