-- Prove2me | solution 1 for Formalism.FG.SolveVAux.seq_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:47.195271+00:00
-- url     : https://prove2.me/submissions/5b074571-06f5-4223-aaaf-a118887bba59

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
variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι] {τ : Type w}
namespace Formalism.FG.SolveVAux
theorem _root_.solution (G : ι → MvPowerSeries τ R) (g : ι → MvPowerSeries ι R) (n : ℕ) :
    seq G g (n + 1) = phi G g (seq G g n) :=
  Function.iterate_succ_apply' _ _ _
end Formalism.FG.SolveVAux
