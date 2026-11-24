-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.stationary_leading_constant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:40.252826+00:00
-- url     : https://prove2.me/submissions/655c3c1a-c3a9-44ac-9d03-0b0be6a1d222

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.LeadingConstant := by
  intro m τ ζ hτ hζ
  have h1 : τ ^ ((m + 1) * (m + 2)) = τ ^ ((m + 1) ^ 2) * τ ^ (m + 1) := by rw [← pow_add]; congr 1; ring
  have h2 : ζ ^ ((m + 2) * (m + 1)) * ζ ^ (m + 1) = ζ ^ ((m + 1) ^ 2) * ζ ^ (2 * (m + 1)) := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  have hm : ((m : ℝ) + 2) ≠ 0 := by positivity
  rw [h1]; field_simp; linarith [h2]
end Formalism.FourierDecayAlt.P
