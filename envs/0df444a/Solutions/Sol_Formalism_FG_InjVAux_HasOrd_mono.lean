-- Prove2me | solution 1 for Formalism.FG.InjVAux.HasOrd.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:05.151156+00:00
-- url     : https://prove2.me/submissions/c6e8a7ce-9e9e-45a0-b11c-61edac3ece37

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
namespace HasOrd
theorem _root_.solution {m n : ℕ} {z : MvPowerSeries τ R} (h : HasOrd n z) (hmn : m ≤ n) :
    HasOrd m z :=
  fun d hd => h d (lt_of_lt_of_le hd hmn)
end HasOrd
end Formalism.FG.InjVAux
