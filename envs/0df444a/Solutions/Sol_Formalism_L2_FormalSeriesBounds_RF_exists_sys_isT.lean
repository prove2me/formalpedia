-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.exists_sys_isT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:36:41.348493+00:00
-- url     : https://prove2.me/submissions/9d0d1f87-9bd9-41c0-a358-258396114235

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_sysExists
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_tExistsUnique


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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {I J : Type} [Fintype I] [Fintype J] (X : Cart V d I J) :
    ∃ (S : Sys X) (t : I → MvPowerSeries I C), S.IsT t := by
  obtain ⟨S, -⟩ := sysExists X (fun c x => if c = x then 1 else 0)
    (by
      intro c x
      split_ifs
      · exact VF.Ge.one
      · exact VF.Ge.zero 0)
    (by
      intro c x h
      rw [if_neg]
      rintro rfl
      exact h rfl)
    (by
      have : (Matrix.of fun c x : I => if c = x then (1 : C) else 0) = 1 := by
        ext c x
        simp [Matrix.one_apply]
      rw [this, Matrix.det_one, V.v.map_one])
  obtain ⟨t, ht, -⟩ := tExistsUnique X S
  exact ⟨S, t, ht⟩
end Formalism.L2.FormalSeriesBounds.RF
