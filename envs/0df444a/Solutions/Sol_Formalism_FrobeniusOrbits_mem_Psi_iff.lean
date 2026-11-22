-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.mem_Psi_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:16:46.768015+00:00
-- url     : https://prove2.me/submissions/60ee4c04-d30e-492e-bae6-b44f0540392e

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
theorem _root_.solution {e : ℕ} (g : GG e) : g ∈ Psi e ↔ g.1.2 = 1 := by
  rw [Psi, MonoidHom.mem_ker]
  rfl
end Formalism.FrobeniusOrbits
