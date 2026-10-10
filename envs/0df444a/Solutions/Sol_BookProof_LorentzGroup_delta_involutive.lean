-- Prove2me | solution 1 for BookProof.LorentzGroup.delta_involutive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:44:56.357977+00:00
-- url     : https://prove2.me/submissions/dfa89065-0eb3-4c27-b2a4-6da8e4982a50

-- Generated from ChapterLorentzGroup.lean — solution of BookProof.LorentzGroup.delta_involutive
import Mathlib
import Definitions.Def_ChapterLorentzGroup
import Theorems.Thm_BookProof_LorentzGroup_eta_mul_self
open BookProof.LorentzGroup




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : ∀ x ∈ Delta, x * x = 1 := by

  rintro x ( rfl | rfl | rfl | rfl ) <;> norm_num [ eta_mul_self ]
