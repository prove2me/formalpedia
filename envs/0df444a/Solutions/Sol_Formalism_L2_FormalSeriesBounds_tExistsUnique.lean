-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.tExistsUnique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:24:06.968704+00:00
-- url     : https://prove2.me/submissions/54fe034a-0ce6-4a1a-aba7-e9f296449209

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_exists_unique
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_contr
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_isT_iff
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {X : Cart V d I J}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (X : Cart V d I J) : TExistsUnique X := by
  intro S
  obtain ⟨t, ⟨h1, h2⟩, hu⟩ := S.contr.exists_unique
  exact ⟨t, (S.isT_iff t).mpr ⟨h1, h2⟩, fun t' ht' => hu t' ((S.isT_iff t').mp ht')⟩
end Formalism.L2.FormalSeriesBounds
