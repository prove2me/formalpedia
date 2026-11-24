-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Contr.noConst_fixPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:49.763902+00:00
-- url     : https://prove2.me/submissions/22ac0163-a6a9-413b-a416-7eefad3d4a3f

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_fixPt_close
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_fixPt_close


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {k : Type*} [Field k] {Z B : Type*}
open Formalism.L2.FormalSeriesBounds.Contr
variable {Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)} (H : Contr Ψ)
include H
namespace Formalism.L2.FormalSeriesBounds.Contr
theorem _root_.solution : NoConst H.fixPt := by
  intro c A hA
  have h := H.fixPt_close 0 c A hA
  simpa using h
end Formalism.L2.FormalSeriesBounds.Contr
