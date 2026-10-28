-- Prove2me | solution 1 for BookProof.FriedrichsExtension.friedrichs_extension_exists_complete
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-27T12:28:29.671685+00:00
-- url     : https://prove2.me/submissions/b01b2c97-3fe1-4033-90b9-50c1ab0327e4

-- Corrected-restatement solution: the target carries `variable [CompleteSpace F]`,
-- so this file's `theorem solution` (same binder set, verified locally against the
-- published mirror) matches the target type exactly. The original
-- `friedrichs_extension_exists` node is Disproved (accepted disproof b9369169) and
-- can never accept a proof.
-- Generated from ChapterFriedrichsExtension.lean — solution of BookProof.FriedrichsExtension.friedrichs_extension_exists_complete
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Theorems.Thm_BookProof_FriedrichsExtension_FormDom_friedrichsResolvent_shift
import Theorems.Thm_BookProof_FriedrichsExtension_FormDom_dom_le_range
import Theorems.Thm_BookProof_HashimotoShiftInvert_invShiftOperator_isPositiveSelfAdjointExtension
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.FriedrichsExtension




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin
-- `friedrichsResolvent*`, `dom_le_range`, `friedrichsResolvent_shift` and the
-- two children proved in `Thm_BookProof_FriedrichsExtension_FormDom_*` all
-- live in `…FriedrichsExtension.FormDom`; without this open the platform
-- answers "Unknown identifier `friedrichsResolvent`" (verdict CE, attempt 1).
open BookProof.FriedrichsExtension.FormDom
open scoped InnerProductSpace ENNReal lp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [CompleteSpace F]

open BookProof.QgOuterFockFL
open BookProof.YangMillsFriedrichs

set_option maxHeartbeats 1000000 in
theorem solution (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsPositiveSelfAdjointExtension P.op A := by
  have hinj : Function.Injective (friedrichsResolvent P) :=
    friedrichsResolvent_injective P hdense
  refine ⟨_, invShiftOperator (friedrichsResolvent P) hinj 1, ?_⟩
  refine invShiftOperator_isPositiveSelfAdjointExtension (friedrichsResolvent P) hinj 1
    (friedrichsResolvent_isSelfAdjoint P) (friedrichsResolvent_pos P) (dom_le_range P) P.op ?_
  intro x
  have hpre : preim (friedrichsResolvent P) ⟨(x : F), dom_le_range P x.2⟩
      = (x : F) + P.op x :=
    preim_eq _ hinj _ (friedrichsResolvent_shift P x)
  rw [invShiftOperator_apply, hpre]
  push_cast
  module
