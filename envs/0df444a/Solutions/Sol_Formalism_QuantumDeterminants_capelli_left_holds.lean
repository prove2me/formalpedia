-- Prove2me | solution 1 for Formalism.QuantumDeterminants.capelli_left_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:26:00.467456+00:00
-- url     : https://prove2.me/submissions/09ac7187-b7fd-4a34-b9a0-5e489fe13614

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Theorems.Thm_Formalism_QuantumDeterminants_quantum_minor_left_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL
noncomputable section
open Formalism Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.QuantumDeterminants
theorem _root_.solution : CapLeft := by
  intro n ε E _ _ f u h
  exact quantum_minor_left_holds n n ε E f id id u h
end Formalism.QuantumDeterminants
