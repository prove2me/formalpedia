-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx5.lambda_threshold_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:24.463922+00:00
-- url     : https://prove2.me/submissions/dfbd3b26-dfd7-4ac1-8551-55caad4e0d98

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx5
namespace Formalism.FourierDecayAlt.P.Jx5
theorem _root_.solution (m i s : ℕ) {C C' κ N I A : ℝ} (hC : 0 ≤ C) (h : C ≤ C') (hκ : 0 ≤ κ) (hN : 0 ≤ N)
    (hI : 0 ≤ I) (hA : 0 ≤ A) :
    0 ≤ Sz.lamThreshold m i s C κ N I A ∧ Sz.lamThreshold m i s C κ N I A ≤ Sz.lamThreshold m i s C' κ N I A := by
  have hC' : 0 ≤ C' := hC.trans h
  unfold Sz.lamThreshold
  constructor
  · positivity
  · gcongr
end Formalism.FourierDecayAlt.P.Jx5
