-- Prove2me | solution 1 for Formalism.G0.DetValP.msMat_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:37.258011+00:00
-- url     : https://prove2.me/submissions/0ce5d82d-8d03-44f3-893f-b7c62adf277c

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal

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
open Formalism Formalism.G0 Formalism.G0.DetValP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι]
namespace Formalism.G0.DetValP
theorem _root_.solution {L : Type} [Field L] {r : ℕ} :
    msMat (1 : GL (Fin r) L) =
      Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then Polynomial.X else 1) := by
  simp [msMat]
end Formalism.G0.DetValP
