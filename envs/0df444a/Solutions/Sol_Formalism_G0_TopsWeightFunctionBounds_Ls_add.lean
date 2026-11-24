-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.Ls_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:43.108895+00:00
-- url     : https://prove2.me/submissions/8e0551ad-34ca-4dec-ae3a-a436cc615cfa

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
theorem _root_.solution (n : ℕ) (T : Finset ℕ) (b t p q : ℕ) :
    ∃ rest, Ls n T b t (p + q) = Ls n T b t p ++ rest :=
  ⟨_, by unfold Ls; rw [List.range_add, List.map_append]⟩
end Formalism.G0.TopsWeightFunctionBounds
