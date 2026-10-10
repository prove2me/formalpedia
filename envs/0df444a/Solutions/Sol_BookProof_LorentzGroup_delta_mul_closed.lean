-- Prove2me | solution 1 for BookProof.LorentzGroup.delta_mul_closed
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:43:54.395112+00:00
-- url     : https://prove2.me/submissions/36d98fee-3fb5-4899-8e6a-8a016df057a9

-- Generated from ChapterLorentzGroup.lean — solution of BookProof.LorentzGroup.delta_mul_closed
import Mathlib
import Definitions.Def_ChapterLorentzGroup
import Theorems.Thm_BookProof_LorentzGroup_eta_mul_self
open BookProof.LorentzGroup




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : ∀ x ∈ Delta, ∀ y ∈ Delta, x * y ∈ Delta := by

  -- every element of `Δ` is one of `1, η, -η, -1`; multiply out the 16 cases
  simp only [Delta, Set.mem_insert_iff, Set.mem_singleton_iff]
  norm_num [eta_mul_self]
