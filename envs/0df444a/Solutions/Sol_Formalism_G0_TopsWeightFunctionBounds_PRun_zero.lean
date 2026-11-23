-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.PRun_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:29.82701+00:00
-- url     : https://prove2.me/submissions/6677b495-8dd3-455b-8425-18ffddcee0a2

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution (n : ℕ) (T : Finset ℕ) (L₂ b t d : ℕ) (u : Fin 0 → ℕ) : PRun n T L₂ b 0 t d u :=
  ⟨fun a => a.elim0, fun l => l.elim0, fun l => l.elim0, fun l => l.elim0, fun l => l.elim0,
    fun h => absurd h (lt_irrefl 0)⟩
end Formalism.G0.TopsWeightFunctionBounds
