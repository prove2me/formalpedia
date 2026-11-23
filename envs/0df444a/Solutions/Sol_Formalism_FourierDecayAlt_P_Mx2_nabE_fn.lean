-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.nabE_fn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:23:54.103647+00:00
-- url     : https://prove2.me/submissions/58f0ed85-9127-46a4-abe8-8de536bd9356

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
    nabE a TT * fnP f fb = fnP f fb * nabE a TT + fnP ((coord vz)⁻¹ * euler vz f) ((coord vzb)⁻¹ * euler vzb fb) := by
  unfold nabE
  rw [zbP, ggiP, multiplierPair_mul, smul_fnP, add_mul, mul_add, multiplierPair_comm, dzP, der_fn]
  abel
end Formalism.FourierDecayAlt.P.Mx2
