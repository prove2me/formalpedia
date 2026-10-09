-- Prove2me | solution 1 for BookProof.ChapterA3.chargeConj_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:03:39.585492+00:00
-- url     : https://prove2.me/submissions/48d2ef36-f0c7-42b2-956a-836afee70825

-- Generated from ChapterA3b.lean — solution of BookProof.ChapterA3.chargeConj_smul
import Mathlib
import Definitions.Def_ChapterA3b
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (c : ℂ) (v : Fin 4 → ℂ) :
    chargeConj (c • v) = conj c • chargeConj v := by

  funext i; simp [chargeConj]
