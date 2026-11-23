-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.b_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:19.298808+00:00
-- url     : https://prove2.me/submissions/465eb769-1fdb-4b10-95a8-08539de946af

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
theorem _root_.solution (ω : ℂ) (hω : ‖ω‖ = 1) (i : ℕ) : ‖ω ^ i - 1‖ ≤ i * ‖ω - 1‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : ω ^ (i + 1) - 1 = ω * (ω ^ i - 1) + (ω - 1) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hω, one_mul]
    push_cast
    linarith
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
