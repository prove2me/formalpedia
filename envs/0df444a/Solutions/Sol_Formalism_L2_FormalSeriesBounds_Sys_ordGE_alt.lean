-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.ordGE_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:03:09.798512+00:00
-- url     : https://prove2.me/submissions/34374efc-5191-417b-be80-a386e7025e5f

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_one_iff

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
namespace Formalism.L2.FormalSeriesBounds
namespace Sys
theorem _root_.solution {t : I → MvPowerSeries I C} (ht : S.IsT t) (c : I) : OrdGE 1 (t c) :=
  (ordGE_one_iff _).2 (ht.1 c)
end Sys
end Formalism.L2.FormalSeriesBounds
