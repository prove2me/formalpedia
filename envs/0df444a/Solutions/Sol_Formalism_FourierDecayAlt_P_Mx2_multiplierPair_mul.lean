-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.multiplierPair_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:26.401292+00:00
-- url     : https://prove2.me/submissions/3fabeac7-54b0-4a13-9246-24482aa0a9f7

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_mulOp_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution (f fb g gb : Fn r) : fnP f fb * fnP g gb = fnP (f * g) (fb * gb) := by
  refine Prod.ext ?_ ?_
  · exact mulOp_mul f g
  · show MulOpposite.op (mulOp gb * mulOp fb) = MulOpposite.op (mulOp (fb * gb))
    rw [mulOp_mul, mul_comm]
end Formalism.FourierDecayAlt.P.Mx2
