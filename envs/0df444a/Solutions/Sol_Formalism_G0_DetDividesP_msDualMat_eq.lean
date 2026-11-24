-- Prove2me | solution 1 for Formalism.G0.DetDividesP.msDualMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:23.71922+00:00
-- url     : https://prove2.me/submissions/8c1bd8e2-b982-4882-98b4-c7ae0238d32e

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides

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
open Polynomial
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0
variable {L : Type} [Field L] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution (g : GL (Fin r) L) : msDualMat g = (nMat g).transpose := rfl
end Formalism.G0.DetDividesP
