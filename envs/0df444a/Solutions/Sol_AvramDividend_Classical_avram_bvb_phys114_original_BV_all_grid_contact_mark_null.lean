-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys114_original_BV_all_grid_contact_mark_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:53:35.347317+00:00
-- url     : https://prove2.me/submissions/75d55d5a-1b8a-4163-90dc-d8e2332845ae

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys111_original_BV_countable_mark_contact_null
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- All exact ruin-contact marks at every cell of a countable
deterministic grid have zero original Lévy mass under Standing-BV. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (a : ℕ → ℕ → ℝ) :
    X.ν {z : ℝ | ∃ n i : ℕ, a n i + z = 0} = 0 := by
  have hset :
      {z : ℝ | ∃ n i : ℕ, a n i + z = 0} =
        Set.range (fun p : ℕ × ℕ => -(a p.1 p.2)) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨n, i, hi⟩
      exact ⟨(n, i), by dsimp; linarith⟩
    · rintro ⟨⟨n, i⟩, rfl⟩
      exact ⟨n, i, by ring⟩
  rw [hset]
  exact avram_bvb_phys111_original_BV_countable_mark_contact_null
    X hStanding hBV _ (Set.countable_range _)
