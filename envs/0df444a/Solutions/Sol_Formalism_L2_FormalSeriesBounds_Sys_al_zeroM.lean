-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.al_zeroM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:58:47.648897+00:00
-- url     : https://prove2.me/submissions/73b32756-2664-4447-889d-8403c4ac7c21

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin

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
theorem _root_.solution (c k : I) : S.al c 0 k = S.tan c k := by
  unfold Sys.al
  rw [(S.curve c).2.1]
  rfl
end Sys
end Formalism.L2.FormalSeriesBounds
