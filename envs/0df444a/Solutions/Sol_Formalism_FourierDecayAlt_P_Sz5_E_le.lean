-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.E_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:31.45915+00:00
-- url     : https://prove2.me/submissions/ff4b998c-d114-4bac-8b64-980a0ffe32f7

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz5
theorem _root_.solution : Real.exp (1/4) ≤ 1.3 := by
  have h1 : Real.exp (1/4) ^ 4 = Real.exp 1 := by
    first
    | (rw [← Real.exp_nat_mul]; norm_num)
    | (rw [← Real.exp_nat_mul]; congr 1; norm_num)
    | (rw [← Real.exp_nat_mul]; congr 1; push_cast; ring)
  have h2 := Real.exp_one_lt_d9
  have h3 : 0 < Real.exp (1/4) := Real.exp_pos _
  by_contra hc
  push_neg at hc
  have ht2 : (1.69:ℝ) < Real.exp (1/4) ^ 2 := by nlinarith
  have ht4 : (2.8561:ℝ) < Real.exp (1/4) ^ 4 := by nlinarith
  linarith
end Formalism.FourierDecayAlt.P.Sz5
