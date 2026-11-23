-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.ee_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:21.716346+00:00
-- url     : https://prove2.me/submissions/c3fc9cfd-c79f-4b8b-ac20-5f157b414884

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous

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
theorem _root_.solution (z : Fin d → ℝ) (τ : Fin d → ℤ) :
    ee z τ = ∏ j, Complex.exp (2 * π * Complex.I * (((τ j : ℝ) : ℂ) * (z j : ℂ))) := by
  unfold ee
  rw [Finset.mul_sum, Complex.exp_sum]
end Formalism.FourierDecayAlt.P.HLsc
