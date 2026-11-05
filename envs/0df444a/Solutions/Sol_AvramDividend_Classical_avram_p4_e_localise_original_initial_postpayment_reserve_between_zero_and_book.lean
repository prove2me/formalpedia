-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:48:29.178395+00:00
-- url     : https://prove2.me/submissions/52d784d5-3d9d-4a6f-a55b-d1acc550fba6

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_initial_postrightpayment_reserve_nonnegative
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact initial right-payment atom lies between zero and the original book reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (ω : Ω) :
    0 ≤ rightLimit D 0 ω ∧
      0 ≤ x + X.X 0 ω - rightLimit D 0 ω ∧
      x + X.X 0 ω - rightLimit D 0 ω ≤ x + X.X 0 ω := by
  have hRightNonneg : 0 ≤ rightLimit D 0 ω := by
    have hm : D 0 ω ≤ rightLimit D 0 ω :=
      dividendStrategy_le_rightLimit D hD.1 ω 0
    simpa only [hD.1.1 ω] using hm
  have hPost : 0 ≤ x + X.X 0 ω - rightLimit D 0 ω :=
    avram_p4_e_localise_original_initial_postrightpayment_reserve_nonnegative
      X x D hD ω
  exact ⟨hRightNonneg, hPost, by linarith⟩
