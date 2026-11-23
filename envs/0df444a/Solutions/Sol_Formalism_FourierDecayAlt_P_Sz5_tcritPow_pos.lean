-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.tcritPow_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:40.531554+00:00
-- url     : https://prove2.me/submissions/9f2fa9b5-499d-4dd2-a3d6-9bb45aeb4cb4

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
theorem _root_.solution (k m : ℕ) (ka rd g VV Vu : ℝ) (hka : 0 < ka) (hrd : 0 < rd) (hg : 0 < g)
    (hVV : 0 < VV) (hVu : 0 < Vu) : 0 < TcritPow k m ka rd g VV Vu := by
  unfold TcritPow
  first
  | positivity
  | (apply div_pos _ hVu
     apply mul_pos _ hVV
     apply mul_pos _ (pow_pos hg _)
     exact mul_pos (inv_pos.mpr (pow_pos hka _)) (Real.rpow_pos_of_pos hrd _))
end Formalism.FourierDecayAlt.P.Sz5
