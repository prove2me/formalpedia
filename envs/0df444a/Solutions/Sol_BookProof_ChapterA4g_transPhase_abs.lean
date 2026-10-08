-- Prove2me | solution 1 for BookProof.ChapterA4g.transPhase_abs
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:34:05.110857+00:00
-- url     : https://prove2.me/submissions/78e99bdf-c3e7-4da1-b134-e4f44178bd18

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.transPhase_abs
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterLorentzTranslation
open BookProof.ChapterLorentzTranslation
open BookProof.ChapterA4g


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

set_option maxHeartbeats 4000000 in
theorem solution (p a : Fin 3 → ℝ) :
    ‖transPhase p a‖ = 1 := by
  simp [BookProof.ChapterA4g.transPhase, Complex.norm_exp]

#print axioms solution

