-- Prove2me | solution 1 for BookProof.ChapterF8.fockEmbed_mem_singleExcitation
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:09:30.364178+00:00
-- url     : https://prove2.me/submissions/99ac177e-b5ec-41c8-9193-f017dbf57e01

-- Generated from ChapterF8.lean — solution of BookProof.ChapterF8.fockEmbed_mem_singleExcitation
import Mathlib
import Definitions.Def_ChapterF8
open BookProof.ChapterF8



noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution {k K : ℕ} (g : Fin k → Fin K) (y : Fin k → ℝ) :
    fockEmbed g y ∈ singleExcitation K := by

  rw [fockEmbed]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨g j, rfl⟩
