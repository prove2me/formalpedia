-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BruhatBigCell.sgn_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:13.054801+00:00
-- url     : https://prove2.me/submissions/2cbf3716-6f3d-44c6-8b1e-bea12d46505f

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell

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
open Formalism.QuantumDeterminants.BruhatBigCell
open GBasic
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.BruhatBigCell
theorem _root_.solution (p : Fin (2 * r + k + 1)) (h : p.val ≠ r + k) : sgn k r p = 1 := by
  unfold sgn; rw [if_neg h]
end Formalism.QuantumDeterminants.BruhatBigCell
