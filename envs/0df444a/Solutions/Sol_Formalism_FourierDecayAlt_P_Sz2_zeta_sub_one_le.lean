-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz2.zeta_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:47.007006+00:00
-- url     : https://prove2.me/submissions/a503975a-d28a-4dbf-8a96-93b1223eb24e

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_partial_le

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
theorem _root_.solution (M : ℕ) (hM : 3 ≤ M) :
    ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ M ≤ 1 + 2 / 2 ^ M := by
  apply Real.tsum_le_of_sum_range_le
  · intro n; positivity
  · intro n
    cases n with
    | zero => simp; positivity
    | succ n =>
      have h := partial_le M hM n
      have : (0 : ℝ) ≤ 4 / 2 ^ M * (1 / (((n : ℝ) + 1) * (n + 2))) := by positivity
      linarith
end Formalism.FourierDecayAlt.P.Sz2
