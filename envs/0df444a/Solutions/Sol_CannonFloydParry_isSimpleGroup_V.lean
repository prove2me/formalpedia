-- Prove2me | solution 1 for CannonFloydParry.isSimpleGroup_V
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T11:54:10.626768+00:00
-- url     : https://prove2.me/submissions/79798902-6653-47e2-b838-5c9d0ea8e99f

import Definitions.Def_CannonFloydParry_V
import Theorems.Thm_CannonFloydParry_exists_mulEquiv_V1_V
import Theorems.Thm_CannonFloydParry_isSimpleGroup_V1
import Mathlib

/-! `V` is simple (CFP p. 243): `V ≅ V₁` and `V₁` is simple (Theorem 6.9). -/

open CannonFloydParry in
theorem solution : IsSimpleGroup V := by
  obtain ⟨e, -⟩ := exists_mulEquiv_V1_V
  have := isSimpleGroup_V1
  exact e.symm.isSimpleGroup
