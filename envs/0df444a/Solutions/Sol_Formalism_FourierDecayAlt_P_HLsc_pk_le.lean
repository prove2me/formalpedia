-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.pk_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:53.204345+00:00
-- url     : https://prove2.me/submissions/1588c4a0-4bf8-4ca7-ad34-aae561135e22

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_fac_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.HLsc
theorem _root_.solution (y : Fin d → ℝ) : pk y ≤ 4 ^ d := by
  have h4 : (4 : ℝ) ^ d = ∏ _j : Fin d, (4 : ℝ) := by simp
  rw [h4]
  unfold pk
  refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
  rw [fac_eq]; linarith [Real.cos_le_one (2 * π * y i)]
end Formalism.FourierDecayAlt.P.HLsc
