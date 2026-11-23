-- Prove2me | solution 1 for Formalism.FG.CongrVAux.zd_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:22.739941+00:00
-- url     : https://prove2.me/submissions/241ad499-57cd-48fc-b1f9-d8ff80bfcd4e

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV

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
open Formalism Formalism.FG Formalism.FG.CongrVAux
open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux
variable {R : Type u} [CommRing R] {τ : Type w}
namespace Formalism.FG.CongrVAux
theorem _root_.solution {d : τ →₀ ℕ} {x y : MvPowerSeries τ R} (hx : Zd d x) (hy : Zd d y) :
    Zd d (x + y) := fun e he => by rw [map_add, hx e he, hy e he, add_zero]
end Formalism.FG.CongrVAux
