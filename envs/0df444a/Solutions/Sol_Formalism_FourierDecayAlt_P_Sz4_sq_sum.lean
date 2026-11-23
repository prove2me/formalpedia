-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.sq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:14.978469+00:00
-- url     : https://prove2.me/submissions/32706318-d0a1-4785-9008-21b25ccd3fb8

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_sum_inv_sq_le_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (n : ℕ) : ∑ d ∈ Ioc 0 n, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 7 / 4 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · norm_num
    · rw [Finset.sum_Ioc_succ_top (by omega)]; norm_num
  · have := sum_inv_sq_le_sub n h
    have h2 : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
end Formalism.FourierDecayAlt.P.Sz4
