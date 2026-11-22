-- Prove2me | solution 1 for Formalism.FG.SolveVAux.low_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:54.746258+00:00
-- url     : https://prove2.me/submissions/2b85fa60-5154-4cce-858f-10e076a903ca

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
theorem _root_.solution (N : ℕ) : Low N (0 : MvPowerSeries τ R) := fun d _ => by simp
end Formalism.FG.SolveVAux
