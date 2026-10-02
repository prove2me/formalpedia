-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.IsShiftInvert.injective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T01:51:47.251013+00:00
-- url     : https://prove2.me/submissions/1d5e17ee-2429-42a3-bfef-d7530e8f9137

-- Generated from ChapterHashimotoShiftInvert.lean — theorem solution
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterComplexShiftCore
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.HashimotoShiftInvert

set_option autoImplicit false



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

open BookProof.HashimotoShiftInvert in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) : Function.Injective R := by
  intro u v huv
  obtain ⟨hu, hu'⟩ := h.2 u
  obtain ⟨hv, hv'⟩ := h.2 v
  rw [← hu', ← hv']
  congr 1
  exact Subtype.ext huv
