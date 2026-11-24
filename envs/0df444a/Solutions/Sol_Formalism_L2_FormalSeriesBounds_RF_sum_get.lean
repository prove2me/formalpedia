-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.sum_get
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:57:01.987829+00:00
-- url     : https://prove2.me/submissions/639ceff4-4187-485d-a4eb-7aed0770ee27

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


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
theorem _root_.solution {α M : Type} [AddCommMonoid M] (l : List α) (f : α → M) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  have h : (fun i : Fin l.length => f (l.get i)) = f ∘ l.get := rfl
  rw [h, ← List.map_ofFn, List.ofFn_get]
end Formalism.L2.FormalSeriesBounds.RF
