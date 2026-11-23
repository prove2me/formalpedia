-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.b_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:02.639334+00:00
-- url     : https://prove2.me/submissions/97b6228e-fc29-493f-b10e-84491efeb82e

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_b_step

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
theorem _root_.solution (c : Cfg) (h : c.Ok) (j : ℕ) (hj : 1 ≤ j) (hm : j ≤ c.m) : 1 ≤ c.b j := by
  rcases Nat.eq_or_lt_of_le hj with h1 | h1
  · rw [← h1]
    exact h.hb1
  · have h2 := b_step c h 1 le_rfl j h1 hm
    linarith [h.hb1]
end Formalism.FourierDecayAlt.P.Sz5
