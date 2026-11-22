-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.HypQD.toHypOdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:02.374812+00:00
-- url     : https://prove2.me/submissions/c0fc72a6-f0a9-4b42-b1f7-21ce44b06964

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_StatementField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
namespace HypQD
theorem _root_.solution {q d : ℕ} (h : HypQD q d) : HypOdd q d := by
  obtain ⟨hq, hd, h3, h7⟩ := h
  refine ⟨hq, hd, ?_, ?_, ?_⟩ <;> omega
end HypQD
end Formalism.TwoAdicCyclotomicDecomposition
