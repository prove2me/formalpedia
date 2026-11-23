-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.vand_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:18.670366+00:00
-- url     : https://prove2.me/submissions/977a5066-1680-4d70-ad21-694ad76560a5

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
theorem _root_.solution (p : ℕ) (x : ℕ → ℝ) :
    Vand (p + 1) x = Vand p x * ∏ i ∈ Icc 1 p, (x i - x (p + 1)) := by
  rw [vand_split p 1 x, vand_one]
  simp only [Finset.Icc_self, Finset.prod_singleton, mul_one, Nat.add_comm 1 p]
end Formalism.FourierDecayAlt.P.Sz5
