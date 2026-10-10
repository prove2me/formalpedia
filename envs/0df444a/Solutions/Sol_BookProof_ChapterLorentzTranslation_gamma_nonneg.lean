-- Prove2me | solution 1 for BookProof.ChapterLorentzTranslation.gamma_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:20:50.261104+00:00
-- url     : https://prove2.me/submissions/66fcccdb-60d3-4318-939d-f6a6326a526e

-- Generated from ChapterLorentzTranslation.lean — solution of BookProof.ChapterLorentzTranslation.gamma_nonneg
import Mathlib
import Definitions.Def_ChapterLorentzTranslation
open BookProof.ChapterLorentzTranslation




open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (w : Fin 3 → ℝ) : 0 ≤ gamma w := Real.sqrt_nonneg _
