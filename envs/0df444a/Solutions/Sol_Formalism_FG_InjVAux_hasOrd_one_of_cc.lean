-- Prove2me | solution 1 for Formalism.FG.InjVAux.hasOrd_one_of_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:21.175573+00:00
-- url     : https://prove2.me/submissions/b5f4d5cb-7487-4e61-a5ce-ee384358153d

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
theorem _root_.solution {z : MvPowerSeries τ R} (hz : constantCoeff z = 0) : HasOrd 1 z := by
  intro d hd
  have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
  subst this
  simpa using hz
end Formalism.FG.InjVAux
