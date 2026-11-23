-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.vand_v_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:09.677078+00:00
-- url     : https://prove2.me/submissions/1d1bc0c4-1ea5-41b6-ab43-0f35ce101114

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_v_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_v_sub


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
theorem _root_.solution (c : Cfg) (h : c.Ok) (p : ℕ) : 0 < Vand p c.v := by
  unfold Vand
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  rw [Finset.mem_Ioc] at hj
  rw [v_sub]
  have hij : (i : ℝ) < (j : ℝ) := by exact_mod_cast hj.1
  have hD : 0 < 4 * c.Del := by linarith [h.hDel]
  exact mul_pos hD (by linarith)
end Formalism.FourierDecayAlt.P.Sz5
