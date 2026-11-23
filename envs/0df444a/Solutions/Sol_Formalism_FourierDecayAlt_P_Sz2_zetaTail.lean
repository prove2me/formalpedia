-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz2.zetaTail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:18.027992+00:00
-- url     : https://prove2.me/submissions/c6fb2732-eed9-42a1-9d8d-4d17f9833bac

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_zeta_sub_one_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz2
theorem _root_.solution : ZetaTail := by
  intro M hM
  have h := zeta_sub_one_le M hM
  have h0 : (0 : ℝ) ≤ ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ M := tsum_nonneg (fun j => by positivity)
  rcases h0.eq_or_lt with h0 | h0
  · rw [← h0]; simp only [Real.log_zero]; positivity
  · have := Real.log_le_sub_one_of_pos h0
    linarith
end Formalism.FourierDecayAlt.P.Sz2
