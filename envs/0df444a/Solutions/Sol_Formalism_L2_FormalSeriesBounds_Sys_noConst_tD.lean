-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.noConst_tD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:23:04.65135+00:00
-- url     : https://prove2.me/submissions/85c763a4-a006-4165-b0e4-5ffb67ba6553

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_subst_linS
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_ordGE_alt

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
  {Xc : Cart V d I J} (S : Sys Xc)
variable {τ : Type} [Fintype τ]
namespace Formalism.L2.FormalSeriesBounds
namespace Sys
theorem _root_.solution (W : τ → I → C) {t : I → MvPowerSeries I C} (ht : S.IsT t) :
    NoConst (fun c => subst (linS W) (t c)) := fun c => ordGE_subst_linS W (S.ordGE_alt ht c)
end Sys
end Formalism.L2.FormalSeriesBounds
