-- Prove2me | solution 1 for Formalism.FG.SolveVAux.hasSubst_of_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:48.174717+00:00
-- url     : https://prove2.me/submissions/6dda1107-85c5-4a49-96e6-2eaf3b7b6b7b

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff

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
theorem _root_.solution {k : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i)) : HasSubst k :=
  hasSubst_of_constantCoeff_zero fun i => (low_one_iff _).1 (hk i)
end Formalism.FG.SolveVAux
