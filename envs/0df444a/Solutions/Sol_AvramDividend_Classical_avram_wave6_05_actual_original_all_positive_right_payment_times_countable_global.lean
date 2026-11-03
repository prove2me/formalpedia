-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_actual_original_all_positive_right_payment_times_countable_global
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:24:23.148327+00:00
-- url     : https://prove2.me/submissions/6f270995-be29-4b0f-890d-1c7f4aea7e09

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_all_nonzero_right_payment_times_countable_on_closed_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

noncomputable section

/-- Every actual original finite-variation dividend strategy has a globally
countable (possibly infinite) family of all positive right-payment times.
The atomless and singular-continuous dividend mass is not affected. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    {t : ℝ≥0 | 0 < rightLimit D t ω - D t ω}.Countable := by
  have hAll : (⋃ n : ℕ,
      {t : ℝ≥0 | t ≤ (n : ℝ≥0) ∧
        0 < rightLimit D t ω - D t ω}).Countable :=
    Set.countable_iUnion (fun n : ℕ =>
      avram_wave6_05_actual_original_all_nonzero_right_payment_times_countable_on_closed_horizon
        X x D hD ω (n : ℝ≥0))
  refine hAll.mono ?_
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
  have htn : t < (n : ℝ≥0) := by exact_mod_cast hn
  apply Set.mem_iUnion.mpr
  refine ⟨n, ?_⟩
  exact ⟨le_of_lt htn, ht⟩
