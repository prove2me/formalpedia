-- Prove2me | solution 1 for BookProof.ComputableScarcity.exists_not_computable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:41:41.058129+00:00
-- url     : https://prove2.me/submissions/e8cdaf6e-65dd-4ad9-84dc-4a034a400ab0

-- Generated from ChapterComputableScarcity.lean — solution of BookProof.ComputableScarcity.exists_not_computable
import Mathlib
import Definitions.Def_ChapterComputableScarcity
import Theorems.Thm_BookProof_ComputableScarcity_exists_differs_infinitely_often_from_all_computable
open BookProof.ComputableScarcity




open Nat.Partrec

open Classical

set_option maxHeartbeats 1000000 in
theorem solution : ∃ f : ℕ → ℕ, ¬ Computable f := by

  obtain ⟨f, hf⟩ := exists_differs_infinitely_often_from_all_computable
  refine ⟨f, fun hcomp => ?_⟩
  have := hf f hcomp
  simp at this
