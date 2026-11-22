-- Prove2me | solution 1 for Formalism.QuantumDeterminants.GBasic.sgn_sig
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:33.217716+00:00
-- url     : https://prove2.me/submissions/e1d6e37a-f462-47b5-a3bb-e9002dbf9c9d

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_val

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
open Formalism.QuantumDeterminants.GBasic
namespace Formalism.QuantumDeterminants.GBasic
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) : sgn k r (sig k r i) = sgn k r i := by
  have hi := i.isLt
  unfold sgn
  rw [sig_val]
  split_ifs <;> first | rfl | (exfalso; omega)
end Formalism.QuantumDeterminants.GBasic
