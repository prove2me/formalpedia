-- Prove2me | solution 1 for Formalism.G0.TypeIIUpP.qfact_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:27.289813+00:00
-- url     : https://prove2.me/submissions/04955061-6305-49b4-879f-bfd52623a44a

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIUp

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
open Formalism Formalism.G0
open Formalism.G0.TypeIIUpP
namespace Formalism.G0.TypeIIUpP
theorem _root_.solution (q n : ℕ) : qfact q (n + 1) = qfact q n * qint q (n + 1) := by
  unfold qfact
  rw [Finset.prod_range_succ]
end Formalism.G0.TypeIIUpP
