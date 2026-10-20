-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.galerkinResolvent_shiftInvert_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:26:41.021735+00:00
-- url     : https://prove2.me/submissions/c2a63581-661e-4dda-8107-115d76ed16fa

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.galerkinResolvent_shiftInvert_tendsto
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Mathlib
import Theorems.Thm_BookProof_HermiteGalerkin_galerkinResolvent_tendsto
import Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvert_isSelfAdjoint
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
open BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}
open BookProof.HashimotoShiftInvert in
theorem solution {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A) (b : HilbertBasis ℕ ℂ F)
    {z : ℂ} (hz : z.im ≠ 0) (u : F) :
    Tendsto (fun m : ℕ => resolvent (galerkinCompression R b m) z u) atTop
      (nhds (resolvent R z u)) := by 
  exact BookProof.HermiteGalerkin.galerkinResolvent_tendsto
    (BookProof.HashimotoShiftInvert.IsShiftInvert.isSelfAdjoint h hsym) b hz u
