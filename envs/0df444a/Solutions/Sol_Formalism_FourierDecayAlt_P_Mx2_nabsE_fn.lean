-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.nabsE_fn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:00.505842+00:00
-- url     : https://prove2.me/submissions/a99166d8-3813-40b9-8e64-1e2565aeba96

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_der_fn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_smul_fnP

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
theorem _root_.solution (a TT : ℝ) (f fb : Fn r) :
    nabsE a TT * fnP f fb = fnP f fb * nabsE a TT - fnP ((coord vzb)⁻¹ * euler vzb f) ((coord vz)⁻¹ * euler vz fb) := by
  unfold nabsE
  rw [zP, ggiP, multiplierPair_mul, smul_fnP, add_mul, mul_add, multiplierPair_comm, dzbP, neg_mul, der_fn, mul_neg]
  abel
end Formalism.FourierDecayAlt.P.Mx2
