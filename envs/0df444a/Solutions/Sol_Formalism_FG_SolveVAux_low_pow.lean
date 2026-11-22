-- Prove2me | solution 1 for Formalism.FG.SolveVAux.low_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:56.779785+00:00
-- url     : https://prove2.me/submissions/fcdfba5d-a1a2-4d5b-b659-c2b73817eb8a

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
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
variable {R : Type u} [CommRing R] {ι : Type v} {τ : Type w}
namespace Formalism.FG.SolveVAux
theorem _root_.solution {p : MvPowerSeries τ R} (hp : Low 1 p) (n : ℕ) : Low n (p ^ n) := by
  induction n with
  | zero => exact low_zero _
  | succ n ih => rw [pow_succ]; exact low_mul ih hp
end Formalism.FG.SolveVAux
