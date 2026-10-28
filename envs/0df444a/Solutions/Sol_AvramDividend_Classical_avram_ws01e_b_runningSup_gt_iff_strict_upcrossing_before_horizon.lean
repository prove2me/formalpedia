-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T23:15:25.991386+00:00
-- url     : https://prove2.me/submissions/bc78ca13-f4cb-47f3-a58d-c614a8d9bb22

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_gt_level_iff_prior_strict_path_hit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_lt_iff_exists_witness
import Theorems.Thm_AvramDividend_Classical_path_value_le_of_strict_prefix_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For spectrally negative Lévy paths, the actual supremum exceeds a
nonnegative level by time t exactly when the strict first-upcrossing clock
is strictly earlier than t. No positive jumps exclude a first crossing
created only at the terminal endpoint, including the zero-time case. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (t : ℝ≥0) :
    b < runningSup X t ω ↔
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)) < (t : ℝ≥0∞) := by
  constructor
  · intro hsup
    by_contra hn
    have hpre : ∀ s : ℝ≥0, s < t → X.X s ω ≤ b := by
      intro s hst
      by_contra hnot
      apply hn
      exact (firstUpcrossing_lt_iff_exists_witness X b ω t).2
        ⟨s, lt_of_not_ge hnot, hst⟩
    have hend : X.X t ω ≤ b :=
      path_value_le_of_strict_prefix_le X b hb ω t hpre
    obtain ⟨s, hst, hxs⟩ :=
      (runningSup_gt_level_iff_prior_strict_path_hit X ω t b).1 hsup
    rcases lt_or_eq_of_le hst with hstrict | heq
    · exact (not_lt_of_ge (hpre s hstrict)) hxs
    · subst s
      exact (not_lt_of_ge hend) hxs
  · intro hτ
    obtain ⟨s, hxs, hst⟩ :=
      (firstUpcrossing_lt_iff_exists_witness X b ω t).1 hτ
    exact (runningSup_gt_level_iff_prior_strict_path_hit X ω t b).2
      ⟨s, le_of_lt hst, hxs⟩
