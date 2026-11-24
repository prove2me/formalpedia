-- Prove2me | solution 1 for Formalism.QuantumDeterminants.group_inverse_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:56.901526+00:00
-- url     : https://prove2.me/submissions/99a88aa9-439d-471f-9bac-610e03109930

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Theorems.Thm_Formalism_QuantumDeterminants_diagonal_inverse_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution : GInv := by
  intro k r z z' hz hz' s hs s' hs' g
  simp only [Gf, diagonal_inverse_holds k r z z' hz hz' s hs s' hs' g]
end Formalism.QuantumDeterminants
