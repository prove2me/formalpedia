-- Prove2me | solution 1 for Formalism.FG.SolveVAux.low_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:42.805802+00:00
-- url     : https://prove2.me/submissions/7c10202a-6be5-45d1-8582-b610595c3539

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV

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
open Formalism Formalism.FG Formalism.FG.SolveVAux
open MvPowerSeries
variable {R : Type u} [CommRing R] {τ : Type w}
namespace Formalism.FG.SolveVAux
theorem _root_.solution {N : ℕ} {p q : MvPowerSeries τ R} (hp : Low N p) (hq : Low N q) :
    Low N (p - q) :=
  fun d hd => by rw [map_sub, hp d hd, hq d hd, sub_zero]
end Formalism.FG.SolveVAux
