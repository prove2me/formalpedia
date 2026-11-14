-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB245_continuous_source_minus_locally_BV_reserve_compact_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:13:36.11565+00:00
-- url     : https://prove2.me/submissions/76a4417d-8bd8-468a-9aba-eedf34a59710

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB244_locally_BV_nonnegative_time_path_bounded_on_compact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original continuous Gaussian source minus locally BV correction stays within a finite reserve band. -/
theorem solution
    (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (d : ℝ≥0 → ℝ)
    (hd : LocallyBoundedVariationOn d Set.univ)
    (x : ℝ) (T : ℝ≥0) :
    ∃ lo hi : ℝ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T,
      lo ≤ x + f t - d t ∧ x + f t - d t ≤ hi := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) T)).exists_bound_of_continuousOn
      (f := f) hf.continuousOn
  obtain ⟨lo, hi, hD⟩ :=
    avram_gbB244_locally_BV_nonnegative_time_path_bounded_on_compact
      d hd T
  refine ⟨x - C - hi, x + C - lo, ?_⟩
  intro t ht
  have hFnorm : ‖f t‖ ≤ C := hC t ht
  have hFabs : |f t| ≤ C := by
    simpa only [Real.norm_eq_abs] using hFnorm
  have hFD := hD t ht
  have hlo := (abs_le.mp hFabs).1
  have hhi := (abs_le.mp hFabs).2
  constructor <;> linarith
