-- Prove2me | solution 1 for Formalism.NG.BlockDetAlt.phiMat_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:43.829604+00:00
-- url     : https://prove2.me/submissions/c68710f2-d642-4214-8018-2b727a16fddd

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}
variable {d : Type} [Fintype d] [DecidableEq d]
variable {d : Type} [Fintype d] [DecidableEq d]
namespace Formalism.NG.BlockDetAlt
theorem _root_.solution (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) {g : Type} [Fintype g]
    [DecidableEq g] (Θ : Matrix g g R') :
    (PowerSeries.constantCoeff).mapMatrix (phiMat R' Θ) = 1 := by
  ext P Q
  simp [phiMat, Matrix.one_apply]
end Formalism.NG.BlockDetAlt
