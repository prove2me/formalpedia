-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ordGE_subst_linS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:08:08.485486+00:00
-- url     : https://prove2.me/submissions/78f2b019-4846-42e1-816b-f8198e1949f1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_linS

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
variable {C : Type*} [Field C] {σ τ : Type*} [Fintype τ]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution [Finite σ] (M : τ → σ → C) {F : MvPowerSeries σ C} {n : ℕ}
    (hF : OrdGE n F) : OrdGE n (subst (linS M) F) := ordGE_subst (ordGE_linS M) hF
end Formalism.L2.FormalSeriesBounds
