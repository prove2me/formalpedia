-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_purejump_finitecap_upperband_expected_spatial_error_arbitrarily_small
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:38:11.369503+00:00
-- url     : https://prove2.me/submissions/d83806d5-a04b-472a-a253-b8abc79b92cf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finitecap_admissible_upperstrip_expected_zero
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
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) :
    ∀ ε : ℝ, 0 < ε → ∃ j : ℕ,
      ∫ ω, ∫ t in Ioo (0 : ℝ) (n : ℝ),
        if C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) <
            riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0 ∂volume ∂P ≤ ε := by
  intro ε hε
  have hlim :=
    avram_f6_original_finitecap_admissible_upperstrip_expected_zero
      X hBV x C hC hFinite hxc D hD n hn
  obtain ⟨j, hj⟩ := (hlim.eventually (Iio_mem_nhds hε)).exists
  exact ⟨j, le_of_lt hj⟩
