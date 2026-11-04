-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_large_raw_uniform_on_prejump_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:13:37.365652+00:00
-- url     : https://prove2.me/submissions/771d722c-b1c8-4ff6-82ce-4f36a9ae0890

import Mathlib.Analysis.Normed.Group.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    (w : ℝ → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ y ∈ Icc 0 v, ∀ z : ℝ, z < 0 →
        |w (y + z) - w y| ≤ M := by
  have hsub : Icc (0 : ℝ) v ⊆ Ici 0 := by
    intro t ht
    exact ht.1
  have hcompact : IsCompact (Icc (0 : ℝ) v) := isCompact_Icc
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn
    (hw_cont.mono hsub)
  have habs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) v) : |w t| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM t ht
  have hMnonneg : 0 ≤ M := by
    have h := habs 0 ⟨le_refl 0, hv⟩
    have hzero : 0 ≤ |w 0| := abs_nonneg _
    linarith
  refine ⟨2 * M, mul_nonneg (by norm_num) hMnonneg, ?_⟩
  intro y hy z hz
  have hwy : |w y| ≤ M := habs y hy
  have hwyz : |w (y + z)| ≤ M := by
    by_cases hneg : y + z < 0
    · rw [hw_neg _ hneg]
      simpa using hMnonneg
    · apply habs
      constructor
      · exact le_of_not_gt hneg
      · linarith [hy.2, hz]
  calc
    |w (y + z) - w y| ≤ |w (y + z)| + |w y| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (w (y + z)) (-w y)
    _ ≤ M + M := add_le_add hwyz hwy
    _ = 2 * M := by ring
