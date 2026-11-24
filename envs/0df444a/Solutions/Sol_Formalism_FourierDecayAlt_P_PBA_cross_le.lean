-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.cross_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:46.806312+00:00
-- url     : https://prove2.me/submissions/2d6ab0b7-1078-4563-a395-552a50d80b55

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : x ^ 2 ≤ A * B) (hx : 0 ≤ x) : 2 * x ≤ A + B := by
  have hAB : 0 ≤ A + B := by linarith
  by_contra hc
  push_neg at hc
  nlinarith [sq_nonneg (A - B), mul_nonneg hAB hx]
end Formalism.FourierDecayAlt.P.PBA
