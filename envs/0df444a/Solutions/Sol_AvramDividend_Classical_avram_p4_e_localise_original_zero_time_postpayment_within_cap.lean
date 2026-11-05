-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_zero_time_postpayment_within_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:58:24.789138+00:00
-- url     : https://prove2.me/submissions/c6c3410e-d802-493f-a39c-0c3e592e7706

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true initial right-payment reserve stays in the cap without assuming an interior start. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω, 0 ≤ x + X.X 0 ω - rightLimit D 0 ω ∧
      ENNReal.ofReal (x + X.X 0 ω - rightLimit D 0 ω) ≤ C := by
  intro ω
  obtain ⟨_, hpost, hle⟩ :=
    avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book
      X x D hD.1 ω
  refine ⟨hpost, ?_⟩
  have hle' : x + X.X 0 ω - rightLimit D 0 ω ≤ x := by
    simpa [X.X_zero ω] using hle
  exact (ENNReal.ofReal_le_ofReal hle').trans hxc
