-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.hpk_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:53:25.688547+00:00
-- url     : https://prove2.me/submissions/d3cf153d-aba9-49ab-a4d7-3094675d28f7

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds

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
open Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.WeylGroupFacts
theorem _root_.solution (i m : Fin (2 * r + k + 1)) :
    Hpk k r i m = if m = tau k r i then sgn k r i else 0 := by
  have hi := i.isLt
  have hm := m.isLt
  unfold Hpk tau sgn
  simp only [Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega | (exfalso; omega) | norm_num
end Formalism.QuantumDeterminants.WeylGroupFacts
