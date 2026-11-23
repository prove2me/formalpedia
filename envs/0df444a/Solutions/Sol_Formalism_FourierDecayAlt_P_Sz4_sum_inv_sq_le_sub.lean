-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.sum_inv_sq_le_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:14.493329+00:00
-- url     : https://prove2.me/submissions/023d8178-92a4-4342-a774-2d2021cc4a84

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub

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
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) : ∑ d ∈ Ioc 0 n, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 7 / 4 - 1 / n := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega)]
    norm_num
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / n - 1 / ((n : ℝ) + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast
    linarith
end Formalism.FourierDecayAlt.P.Sz4
