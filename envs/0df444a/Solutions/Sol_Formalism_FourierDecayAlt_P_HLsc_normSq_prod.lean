-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.normSq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:35.506472+00:00
-- url     : https://prove2.me/submissions/9d58100f-167e-4ab4-bdd4-e5c81cc7009b

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
theorem _root_.solution (n : ℕ) (y : Fin d → ℝ) :
    ‖∏ j, (1 + Complex.exp (2 * π * Complex.I * (y j : ℂ))) ^ n‖ ^ 2 = pk y ^ n := by
  unfold pk
  rw [norm_prod, ← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [norm_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
end Formalism.FourierDecayAlt.P.HLsc
