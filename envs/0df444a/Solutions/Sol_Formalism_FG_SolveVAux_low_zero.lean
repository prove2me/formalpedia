-- Prove2me | solution 1 for Formalism.FG.SolveVAux.low_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:25.03781+00:00
-- url     : https://prove2.me/submissions/55c9fe4b-7972-4f34-90b3-326c32dc4b3e

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
theorem _root_.solution (p : MvPowerSeries τ R) : Low 0 p := fun _ hd => absurd hd (Nat.not_lt_zero _)
end Formalism.FG.SolveVAux
