-- Prove2me | solution 1 for BookProof.GaugeFixing.matrixModelIntegral_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T14:45:28.241511+00:00
-- url     : https://prove2.me/submissions/86883f8f-5a14-4b08-8135-53f124ea5c29

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.matrixModelIntegral_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem solution :
    ∃ X : Mat2, matrixModelIntegral.int X ≠ 0 := by
  refine ⟨Pm, ?_⟩
  show Pm 1 0 ≠ 0
  simp [Pm]
