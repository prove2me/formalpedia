-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.snocF_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:06.409868+00:00
-- url     : https://prove2.me/submissions/0f78f772-d27a-4fad-8cb2-587e4f67d8be

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
theorem _root_.solution {j : ℕ} (u : Fin j → ℕ) (v : ℕ) (l : Fin (j + 1)) (h : ¬ l.val < j) :
    snocF u v l = v := dif_neg h
end Formalism.G0.TopsWeightFunctionBounds
