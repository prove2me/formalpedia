-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB32_positive_gaussian_original_barrier_stopped_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:57:35.70619+00:00
-- url     : https://prove2.me/submissions/e1a9cd58-ab99-4124-bbe3-9dd1e85c66f2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB32_original_positive_gaussian_full_path_standing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_avram_gbB32_original_cap_barrier_full_continuity
import Theorems.Thm_AvramDividend_Classical_avram_gbB32_original_risk_continuity_of_components
import Theorems.Thm_AvramDividend_Classical_avram_gbB31_original_risk_lower_cutoff_rightCont_stop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (S : Set ℝ≥0) (hS : S.Countable) (hDense : Dense S)
    (h0 : (0 : ℝ≥0) ∈ S) (H : ℝ≥0) (b : ℝ) :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      Y.c = 2 ∧ Y.σ = 1 ∧ Y.ν = 0 ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      (∀ ω, Continuous (fun t : ℝ≥0 =>
        riskProcess Y (1 / 8 : ℝ)
          (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ∧
      IsStoppingTime 𝓕.rightCont (fun ω : ℝ≥0 → ℝ =>
        WithTop.some (sInf ((Icc (0 : ℝ≥0) H ∩
          (fun t : ℝ≥0 => -(riskProcess Y (1 / 8 : ℝ)
            (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
            Ici (-b)) ∪ {H}))) := by 
  obtain ⟨𝓕, Y, hPath, hc, hσ, hν, hStand, hUBV, hYCont⟩ :=
    avram_gbB32_original_positive_gaussian_full_path_standing
  let C : ℝ := 1 / 8
  let D : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
    barrierStrategy Y C C
  have hD : IsDividendStrategy 𝓕 D :=
    barrierStrategy_isDividendStrategy_nonnegative_barrier Y C C
      (by norm_num [C]) (by norm_num [C])
  have hDCont : ∀ ω, Continuous (fun t : ℝ≥0 => D t ω) :=
    avram_gbB32_original_cap_barrier_full_continuity Y C
  have hRiskCont : ∀ ω, Continuous
      (fun t : ℝ≥0 => riskProcess Y C D t ω) :=
    avram_gbB32_original_risk_continuity_of_components
      Y C D hYCont hDCont
  have hStop :=
    avram_gbB31_original_risk_lower_cutoff_rightCont_stop
      Y C D hD hRiskCont S hS hDense h0 H b
  exact ⟨𝓕, Y, hc, hσ, hν, hStand, hUBV, hRiskCont, hStop⟩
