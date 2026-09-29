-- Prove2me | solution 1 for CannonFloydParry.isSimpleGroup_T
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T20:20:32.567375+00:00
-- url     : https://prove2.me/submissions/e61e1b4b-2fd7-4ff5-baf7-e0dd535a386f

import Theorems.Thm_CannonFloydParry_isSimpleGroup_T1
import Theorems.Thm_CannonFloydParry_exists_mulEquiv_T1_T
import Mathlib

/-! Lemma 5.3 from Lemma 5.2; Corollary 5.9 from Lemma 5.3 and Theorem 5.8; the goal. -/

namespace CannonFloydParry.S5

/-- The goal: `T` is simple. -/
theorem isSimpleGroup_T' : IsSimpleGroup T := by
  obtain ⟨e, -⟩ := exists_mulEquiv_T1_T
  have := isSimpleGroup_T1
  exact e.symm.isSimpleGroup

end CannonFloydParry.S5

open CannonFloydParry

theorem solution : IsSimpleGroup T :=
  CannonFloydParry.S5.isSimpleGroup_T'
