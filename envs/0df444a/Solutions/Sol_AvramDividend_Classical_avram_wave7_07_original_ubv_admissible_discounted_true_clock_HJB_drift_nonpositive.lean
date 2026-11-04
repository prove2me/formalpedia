-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_true_clock_HJB_drift_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:03:33.972763+00:00
-- url     : https://prove2.me/submissions/43dd599f-fcd3-475a-aeba-1dd8d64f0e41

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_true_clock_predictable_weight_HJB_generator_drift_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_time_exponential_discount_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original actual physical predictable clock has nonpositive discounted
full compensated generator-HJB drift for admissible UBV strategies. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : ENNReal.ofReal v < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0)
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable (fun p => Real.exp (-(q * (p.1 : ℝ))) * R p) μ ∧
      (∫ p, Real.exp (-(q * (p.1 : ℝ))) * R p ∂μ) ≤ 0 := by
  classical
  intro Y ρ R
  have hv0 : 0 ≤ v := by linarith
  obtain ⟨Rcap, hvRcap, hRcapC, hwRcap⟩ :=
    avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists w C v hv0 hv hw
  have hGenR : ∀ y : ℝ, 0 < y → y < Rcap →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy0 hyRcap
    have hYcap : ENNReal.ofReal y < C :=
      (ENNReal.ofReal_le_ofReal hyRcap.le).trans_lt hRcapC
    exact hw_gen y hy0 hYcap
  have hWeight (p : ℝ≥0 × Ω) :
      0 ≤ Real.exp (-(q * (p.1 : ℝ))) ∧
      Real.exp (-(q * (p.1 : ℝ))) ≤ 1 := by
    constructor
    · exact Real.exp_nonneg _
    · apply Real.exp_le_one_iff.mpr
      have ht : 0 ≤ (p.1 : ℝ) := NNReal.coe_nonneg _
      exact neg_nonpos.mpr (mul_nonneg hq ht)
  exact avram_wave7_07_true_clock_predictable_weight_HJB_generator_drift_nonpositive
    X x D hD.1.1 w Rcap u v δ hwRcap hw_cont hw_neg
    hu hδ hδone huv hvRcap q T hGenR
    (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ))))
    (avram_wave7_07_original_predictable_time_exponential_discount_measurable
      (𝓕 := 𝓕) q) hWeight
