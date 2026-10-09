-- Prove2me | solution 1 for BookProof.ChapterGaugeUnconstrainedSpectrum.diagOp_injective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T10:38:25.734979+00:00
-- url     : https://prove2.me/submissions/5232f177-3cea-4076-88f8-693ffe165b69

import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterAbelianDiagonalCountable

theorem solution {X : Type*} :
    Function.Injective (BookProof.ChapterGaugeUnconstrainedSpectrum.diagOp (X := X)) := by
  intro d e h
  funext x
  have h1 := congrArg (fun T => T (fun _ => (1 : ℂ)) x) h
  simpa [BookProof.ChapterGaugeUnconstrainedSpectrum.diagOp] using h1
