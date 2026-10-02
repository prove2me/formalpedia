-- Prove2me | solution 1 for BookProof.ChapterH8.sirk_krylov_tower
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T02:39:28.19792+00:00
-- url     : https://prove2.me/submissions/80d777a1-63b4-41c2-971c-db3d3fb1bf09

import Mathlib
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterH5

set_option autoImplicit false

open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6 BookProof.ChapterH8 in
theorem solution {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (H : E →ₗ[K] E) (v : E) (n : ℕ) :
    krylovSpan H v n ≤ krylovSpan H v (n + 1) := by
  unfold krylovSpan
  apply Submodule.span_mono
  rintro x ⟨i, hi, rfl⟩
  exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩
