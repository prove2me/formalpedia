-- Prove2me | solution 1 for BookProof.ChapterA.HasQuaternionicRImaginary.hasCommutingRImaginary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:28:15.980574+00:00
-- url     : https://prove2.me/submissions/16dd7189-cec9-418b-aa4c-e4e1570ca011

-- Generated from ChapterA1h.lean — solution of BookProof.ChapterA.HasQuaternionicRImaginary.hasCommutingRImaginary
import Mathlib
import Definitions.Def_ChapterA1h
import Definitions.Def_Complexification
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification
open BookProof.ChapterA.AntiUnitary

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

set_option maxHeartbeats 1000000 in
theorem solution {M : System ℝ W}
    (h : HasQuaternionicRImaginary M) : HasCommutingRImaginary M := by

  obtain ⟨J, _, hJ, _, _⟩ := h
  exact ⟨J, hJ⟩
