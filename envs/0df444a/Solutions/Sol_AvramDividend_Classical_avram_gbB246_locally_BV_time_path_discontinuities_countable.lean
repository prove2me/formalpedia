-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB246_locally_BV_time_path_discontinuities_countable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:23:24.661183+00:00
-- url     : https://prove2.me/submissions/dfe6d14c-1cd1-407c-ac76-92d3f553fc49

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original local BV correction has countably many time discontinuities. -/
theorem solution
    (f : ℝ≥0 → ℝ)
    (hf : LocallyBoundedVariationOn f Set.univ) :
    Set.Countable {t : ℝ≥0 | ¬ ContinuousAt f t} := by
  obtain ⟨p, q, hp, hq, hrep⟩ :=
    hf.exists_monotoneOn_sub_monotoneOn
  have hpmon : Monotone p := by
    intro a b hab
    exact hp (Set.mem_univ _) (Set.mem_univ _) hab
  have hqmon : Monotone q := by
    intro a b hab
    exact hq (Set.mem_univ _) (Set.mem_univ _) hab
  have hpcount : Set.Countable {t : ℝ≥0 | ¬ ContinuousAt p t} :=
    hpmon.countable_not_continuousAt
  have hqcount : Set.Countable {t : ℝ≥0 | ¬ ContinuousAt q t} :=
    hqmon.countable_not_continuousAt
  apply (hpcount.union hqcount).mono
  intro t ht
  by_contra hbad
  have hpcont : ContinuousAt p t := by
    by_contra h
    exact hbad (Or.inl h)
  have hqcont : ContinuousAt q t := by
    by_contra h
    exact hbad (Or.inr h)
  have hfcont : ContinuousAt f t := by
    rw [hrep]
    exact hpcont.sub hqcont
  exact ht hfcont
