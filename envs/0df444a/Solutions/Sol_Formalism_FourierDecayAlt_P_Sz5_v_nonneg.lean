-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.v_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:25.842411+00:00
-- url     : https://prove2.me/submissions/ab9386b2-5700-4672-8ade-fefb88ef9e0b

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
theorem _root_.solution (c : Cfg) (h : c.Ok) (i : ℕ) (hi : i + 1 ≤ c.k) : 0 ≤ c.v i := by
  have hki : (i : ℝ) + 1 ≤ (c.k : ℝ) := by exact_mod_cast hi
  have h3 : 0 ≤ (c.k : ℝ) - 1 - (i : ℝ) := by linarith
  have h4 : 0 ≤ c.Del := by linarith [h.hDel]
  have h5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) h4) h3
  unfold Cfg.v
  linarith [h.hv0]
end Formalism.FourierDecayAlt.P.Sz5
