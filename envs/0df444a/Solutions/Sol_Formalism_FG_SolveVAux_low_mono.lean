-- Prove2me | solution 1 for Formalism.FG.SolveVAux.low_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:05.063849+00:00
-- url     : https://prove2.me/submissions/7c9abdc0-7d89-4c02-8e2f-a57b933dd98c

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
theorem _root_.solution {M N : ℕ} (h : M ≤ N) {p : MvPowerSeries τ R} (hp : Low N p) : Low M p :=
  fun d hd => hp d (lt_of_lt_of_le hd h)
end Formalism.FG.SolveVAux
