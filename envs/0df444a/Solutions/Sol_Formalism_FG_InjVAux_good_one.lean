-- Prove2me | solution 1 for Formalism.FG.InjVAux.good_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:03.42245+00:00
-- url     : https://prove2.me/submissions/c4617141-f705-4d58-aef1-f0d974335168

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Theorems.Thm_Formalism_FG_InjVAux_hasOrd_zero_left
import Theorems.Thm_Formalism_FG_InjVAux_hasOrd_zero

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
theorem _root_.solution (N : ℕ) : Good N 0 (1 : MvPowerSeries τ R) 1 :=
  ⟨hasOrd_zero_left _, hasOrd_zero_left _, by rw [sub_self]; exact hasOrd_zero _⟩
end Formalism.FG.InjVAux
