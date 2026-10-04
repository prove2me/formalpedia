-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.isShiftInvert_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:12:28.809948+00:00
-- url     : https://prove2.me/submissions/9c26d2d8-fc36-49c2-8db3-5504f11e7cb4

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterComplexShiftCore

set_option autoImplicit false

open BookProof.HashimotoShiftInvert in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R S : F →L[ℂ] F}
    (hR : IsShiftInvert A γ R) (hS : IsShiftInvert A γ S) : R = S := by
  ext u
  obtain ⟨h, hu⟩ := hR.2 u
  have key := hS.1 ⟨R u, h⟩
  rw [hu] at key
  exact key.symm
