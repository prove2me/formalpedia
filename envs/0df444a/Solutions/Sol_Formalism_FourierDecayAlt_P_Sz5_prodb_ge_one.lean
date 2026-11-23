-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.prodb_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:57.340883+00:00
-- url     : https://prove2.me/submissions/297e122b-05cf-465b-909f-25f06a771a92

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_b_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_one_le_prod_real

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
theorem _root_.solution (c : Cfg) (h : c.Ok) : 1 ≤ c.prodb := by
  unfold Cfg.prodb
  apply one_le_prod_real
  intro j hj
  rw [Finset.mem_Icc] at hj
  exact b_ge_one c h j hj.1 hj.2
end Formalism.FourierDecayAlt.P.Sz5
