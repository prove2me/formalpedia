-- Prove2me | solution 1 for Formalism.FG.InjVAux.hasOrd_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:21.026106+00:00
-- url     : https://prove2.me/submissions/5588d1f8-3ed3-447a-a98d-2b18989fc0a2

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG
open Formalism.FG.InjVAux
open MvPowerSeries
variable {R : Type*} [CommRing R] {τ : Type*}
namespace Formalism.FG.InjVAux
theorem _root_.solution (n : ℕ) : HasOrd n (0 : MvPowerSeries τ R) := fun _ _ => by simp
end Formalism.FG.InjVAux
