-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.log_tp_diff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:27.669867+00:00
-- url     : https://prove2.me/submissions/8b1dabaa-fe99-4e77-a6e8-64308f8913a9

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
theorem _root_.solution (k m : ℕ) (ka rd g VV V V' : ℝ) (hka : 0 < ka) (hrd : 0 < rd) (hg : 0 < g)
    (hVV : 0 < VV) (hV : 0 < V) (hV' : 0 < V') :
    Real.log (TcritPow k m ka rd g VV V) - Real.log (TcritPow k m ka rd g VV V') =
      Real.log (V' / V) := by
  have key : ∀ P : ℝ, 0 < P → Real.log (P / V) - Real.log (P / V') = Real.log (V' / V) := by
    intro P hP
    rw [Real.log_div hP.ne' hV.ne', Real.log_div hP.ne' hV'.ne', Real.log_div hV'.ne' hV.ne']
    ring
  unfold TcritPow
  exact key _ (by positivity)
end Formalism.FourierDecayAlt.P.Sz5
