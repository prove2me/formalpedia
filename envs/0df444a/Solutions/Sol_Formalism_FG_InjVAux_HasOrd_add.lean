-- Prove2me | solution 1 for Formalism.FG.InjVAux.HasOrd.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:47.518802+00:00
-- url     : https://prove2.me/submissions/48ee4222-6be2-42c6-9f03-1efea5f6ff87

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
theorem _root_.solution {n : ℕ} {x y : MvPowerSeries τ R} (hx : HasOrd n x) (hy : HasOrd n y) :
    HasOrd n (x + y) :=
  fun d hd => by rw [map_add, hx d hd, hy d hd, add_zero]
end HasOrd
end Formalism.FG.InjVAux
