-- Prove2me | solution 1 for Formalism.FG.SolveVAux.low_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:53.804844+00:00
-- url     : https://prove2.me/submissions/73731895-0ec8-454f-aaa8-123f7a7a9db2

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul

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
theorem _root_.solution {M : ℕ} {a a' b b' : MvPowerSeries τ R} (ha : Low M (a - a'))
    (hb : Low M (b - b')) : Low M (a * b - a' * b') := by
  have e : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [e]
  refine low_add ?_ ?_
  · simpa using low_mul ha (low_zero b)
  · simpa using low_mul (low_zero a') hb
end Formalism.FG.SolveVAux
