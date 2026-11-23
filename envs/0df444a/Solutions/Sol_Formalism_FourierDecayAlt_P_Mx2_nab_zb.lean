-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.nab_zb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:28.80747+00:00
-- url     : https://prove2.me/submissions/8c6de22a-670f-45e6-9c4b-afea48f4ddbb

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eulerCoord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_vz_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nabE_fn

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
theorem _root_.solution (a TT : ℝ) : nabE a TT * (zbP : Pr r) = zbP * nabE a TT := by
  rw [zbP, nabE_fn, (eulerCoord r vz vzb 0).1, (eulerCoord r vzb vz 0).1, if_neg vz_ne, if_neg vz_ne.symm]
  simp only [mul_zero]
  have h0 : mulOp (0 : Fn r) = 0 := by ext h : 1; simp [mulOp]
  have : (fnP 0 0 : Pr r) = 0 := by
    refine Prod.ext h0 ?_
    show MulOpposite.op (mulOp (0 : Fn r)) = 0
    rw [h0]; rfl
  rw [this, add_zero]
end Formalism.FourierDecayAlt.P.Mx2
