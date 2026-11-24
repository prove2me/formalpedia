-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.snocF_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:25.199522+00:00
-- url     : https://prove2.me/submissions/3aa93a9e-ab74-44d3-a75d-ed31c6536660

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
theorem _root_.solution {j : ℕ} (u : Fin j → ℕ) (v : ℕ) (l : Fin (j + 1)) (h : l.val < j) :
    snocF u v l = u ⟨l.val, h⟩ := dif_pos h
end Formalism.G0.TopsWeightFunctionBounds
