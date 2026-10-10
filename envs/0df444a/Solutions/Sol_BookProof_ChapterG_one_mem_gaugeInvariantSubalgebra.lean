-- Prove2me | solution 1 for BookProof.ChapterG.one_mem_gaugeInvariantSubalgebra
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:21:51.992706+00:00
-- url     : https://prove2.me/submissions/db201fd2-617f-412d-b445-e2448d19bc3a

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.one_mem_gaugeInvariantSubalgebra
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix

set_option maxHeartbeats 1000000 in
theorem solution {X Y : Type*} (π : X → Y) :
    (1 : X → ℝ) ∈ gaugeInvariantSubalgebra ℝ π := by

  intro g _ x; rfl
