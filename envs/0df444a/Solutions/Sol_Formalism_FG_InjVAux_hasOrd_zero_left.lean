-- Prove2me | solution 1 for Formalism.FG.InjVAux.hasOrd_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:56.394983+00:00
-- url     : https://prove2.me/submissions/f73bb6f5-ef04-48e1-a33b-2ecf133991f6

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
theorem _root_.solution (z : MvPowerSeries τ R) : HasOrd 0 z :=
  fun _ hd => absurd hd (Nat.not_lt_zero _)
end Formalism.FG.InjVAux
