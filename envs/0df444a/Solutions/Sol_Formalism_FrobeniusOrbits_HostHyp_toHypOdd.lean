-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.HostHyp.toHypOdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:13:56.226339+00:00
-- url     : https://prove2.me/submissions/5b02c58c-b1d0-46f6-9cff-c30fdb361bdc

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_FrobeniusOrbits_Statement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.FrobeniusOrbits
namespace HostHyp
theorem _root_.solution {q d : ℕ} (h : HostHyp q d) : HypOdd q d := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  exact ⟨h1, h2, by omega, by omega, by omega⟩
end HostHyp
end Formalism.FrobeniusOrbits
