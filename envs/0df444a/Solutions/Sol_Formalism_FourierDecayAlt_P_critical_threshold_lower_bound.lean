-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.critical_threshold_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:02.66782+00:00
-- url     : https://prove2.me/submissions/0da4476f-6565-42e2-a33d-bf5b268d6598

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_tcritLower_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_bracket_bound_alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_edgeFactors
import Theorems.Thm_Formalism_FourierDecayAlt_P_vandermondeNonTop
import Theorems.Thm_Formalism_FourierDecayAlt_P_vandermondeTop
import Theorems.Thm_Formalism_FourierDecayAlt_P_vandermondeWords


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.TcritLower := Sz5.tcritLower_of bracket_bound_alt vandermondeNonTop vandermondeTop edgeFactors vandermondeWords
end Formalism.FourierDecayAlt.P
