-- Prove2me | solution 1 for Formalism.FG.SolveVAux.low_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:38.198222+00:00
-- url     : https://prove2.me/submissions/cace4943-4ed3-48d5-8e2f-b6933f199312

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
theorem _root_.solution {N : ℕ} {p : MvPowerSeries τ R} (hp : Low N p) : Low N (-p) :=
  fun d hd => by rw [map_neg, hp d hd, neg_zero]
end Formalism.FG.SolveVAux
