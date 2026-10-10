-- Prove2me | solution 1 for BookProof.ChapterLpScaleMeasure.scaleUnitary_coeFn
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:26:22.384557+00:00
-- url     : https://prove2.me/submissions/a91c2619-015f-4792-bf6e-f321450a3bd6

import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterLpScaleMeasure
open BookProof.ChapterLpScaleMeasure
noncomputable section
open MeasureTheory ENNReal
open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {nu : Measure α} {c : ENNReal}

theorem solution (hc0 : c ≠ 0) (hctop : c ≠ ⊤) (u : Lp ℂ 2 (c • nu)) :
    (scaleUnitary hc0 hctop u : α → ℂ) =ᵐ[nu] fun x => (scaleConst c : ℂ) * (u : α → ℂ) x :=
  scaleLin_coeFn hc0 hctop u
