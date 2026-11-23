-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.multiplierPair_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:06.694984+00:00
-- url     : https://prove2.me/submissions/a1bab861-b585-44f1-b700-4a10b305c76c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_add

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
theorem _root_.solution (f fb : Fn r) : -fnP f fb = fnP (-f) (-fb) := by
  rw [neg_eq_iff_add_eq_zero, multiplierPair_add]; simp
  refine Prod.ext ?_ ?_
  · show mulOp (0 : Fn r) = 0
    ext h : 1; simp [mulOp]
  · show MulOpposite.op (mulOp (0 : Fn r)) = 0
    have : mulOp (0 : Fn r) = 0 := by ext h : 1; simp [mulOp]
    rw [this]; rfl
end Formalism.FourierDecayAlt.P.Mx2
