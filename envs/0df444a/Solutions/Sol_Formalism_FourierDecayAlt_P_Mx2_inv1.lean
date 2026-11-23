-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.inv1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:24.553311+00:00
-- url     : https://prove2.me/submissions/5ee72adf-1ee2-41b7-a894-0ceea5b92bfe

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_one

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
theorem _root_.solution (f fb : Fn r) (h : f ≠ 0) (hb : fb ≠ 0) : fnP f fb * fnP f⁻¹ fb⁻¹ = 1 := by
  rw [multiplierPair_mul, mul_inv_cancel₀ h, mul_inv_cancel₀ hb, multiplierPair_one]
end Formalism.FourierDecayAlt.P.Mx2
