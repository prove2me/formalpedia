-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54cp_true_stopped_upperstrip_prepost_occupation_integral_eq_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:32:23.942992+00:00
-- url     : https://prove2.me/submissions/eb32edcf-d217-43b0-b06d-12eaf3299bad

import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_riskProcess_eq_postpayment_reserve_lebesgue_ae
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω) :
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
        b < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) =
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
        b < x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) := by
  have hAe : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), 0 ≤ t →
      riskProcess X x D (Real.toNNReal t) ω =
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω :=
    avram_wave7_18_original_riskProcess_eq_postpayment_reserve_lebesgue_ae
      X x D hD ω
  have hAeR : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      0 ≤ t → riskProcess X x D (Real.toNNReal t) ω =
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω :=
    Filter.Eventually.filter_mono (ae_mono Measure.restrict_le_self) hAe
  have hAeRestr : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      riskProcess X x D (Real.toNNReal t) ω =
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω := by
    filter_upwards [hAeR,
      ae_restrict_mem measurableSet_Ioo] with t hEq ht
    exact hEq (le_of_lt ht.1)
  apply integral_congr_ae
  filter_upwards [hAeRestr] with t hEq
  simp only [hEq]
