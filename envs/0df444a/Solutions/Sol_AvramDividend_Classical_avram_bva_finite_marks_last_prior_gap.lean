-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_finite_marks_last_prior_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:56:02.033943+00:00
-- url     : https://prove2.me/submissions/6169acd8-de5d-4ebe-b489-ecf5046faf74

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (S : Finset ℝ≥0) (t : ℝ≥0) (ht : 0 < t) :
    ∃ s : ℝ≥0, s < t ∧
      ∀ u ∈ S, u < t → u ≤ s := by
  classical
  let F : Finset ℝ≥0 := S.filter (fun u => u < t)
  by_cases hF : F.Nonempty
  · refine ⟨F.max' hF, ?_, ?_⟩
    · have hm := Finset.max'_mem F hF
      exact (Finset.mem_filter.mp hm).2
    · intro u hu hut
      have hmem : u ∈ F := Finset.mem_filter.mpr ⟨hu, hut⟩
      exact Finset.le_max' F u hmem
  · refine ⟨0, ht, ?_⟩
    intro u hu hut
    have hmem : u ∈ F := Finset.mem_filter.mpr ⟨hu, hut⟩
    exact False.elim (hF ⟨u, hmem⟩)
