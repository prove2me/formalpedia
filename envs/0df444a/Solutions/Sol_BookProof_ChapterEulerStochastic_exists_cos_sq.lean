-- Prove2me | solution 1 for BookProof.ChapterEulerStochastic.exists_cos_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:52:14.590484+00:00
-- url     : https://prove2.me/submissions/1d83d404-dbdf-4abc-999f-9b007bf31534

-- Generated from ChapterEulerStochastic.lean — solution of BookProof.ChapterEulerStochastic.exists_cos_sq
import Mathlib
import Definitions.Def_ChapterEulerStochastic
open BookProof.ChapterEulerStochastic



open scoped Matrix BigOperators

set_option maxHeartbeats 1000000 in
theorem solution {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ a : ℝ, Real.cos a ^ 2 = p := by

      exact ⟨ Real.arccos ( Real.sqrt p ), by rw [ Real.cos_arccos ] <;> nlinarith [
                                              Real.mul_self_sqrt hp0 ] ⟩
