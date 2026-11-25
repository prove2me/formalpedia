-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_linS_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:08:40.145575+00:00
-- url     : https://prove2.me/submissions/8a2e82fb-5fb7-42fa-9592-33aa8b8dbe77

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_hasSubst_linS

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
theorem _root_.solution [Finite σ] (M : τ → σ → C) (F G : MvPowerSeries σ C) :
    subst (linS M) (F - G) = subst (linS M) F - subst (linS M) G := subst_sub (hasSubst_linS M) F G
end Formalism.L2.FormalSeriesBounds
