-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.vand_head
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:03.097161+00:00
-- url     : https://prove2.me/submissions/027e36a8-9656-4468-8703-6caec2d8a467

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_vand_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_vand_one

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
theorem _root_.solution (q : ℕ) (x : ℕ → ℝ) :
    Vand (q + 1) x = (∏ j ∈ Icc 1 q, (x 1 - x (j + 1))) * Vand q (fun j => x (j + 1)) := by
  rw [Nat.add_comm q 1, vand_split 1 q x, vand_one]
  simp only [Finset.Icc_self, Finset.prod_singleton, one_mul]
end Formalism.FourierDecayAlt.P.Sz5
