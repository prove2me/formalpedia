-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.hs_tail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:13.751032+00:00
-- url     : https://prove2.me/submissions/6ce7dec1-50f3-4084-a322-07ffb8315d13

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_hs_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz3
theorem _root_.solution (p : ℕ) (hp : 1 ≤ p) : hs (2 * p) - hs p ≤ 7 / 10 - 1 / (4 * (p : ℝ) + 1) := by
  induction p, hp using Nat.le_induction with
  | base =>
    have h2 : hs (2 * 1) = hs 1 + 1 / ((1 : ℝ) + 1) := by
      have := hs_succ 1
      simpa using this
    rw [h2]; norm_num
  | succ n hn ih =>
    have h1 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    rw [h1, hs_succ, hs_succ, hs_succ]
    push_cast
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have e1 : 1 / ((2 : ℝ) * n + 1) + 1 / (2 * n + 1 + 1) - 1 / (n + 1) =
        1 / ((2 * n + 1) * (2 * n + 2)) := by
      field_simp; ring
    have e2 : 1 / (4 * (n : ℝ) + 1) - 1 / (4 * (n + 1) + 1) = 4 / ((4 * n + 1) * (4 * n + 5)) := by
      field_simp; ring
    have key : 1 / (((2 : ℝ) * n + 1) * (2 * n + 2)) ≤ 4 / ((4 * n + 1) * (4 * n + 5)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
end Formalism.FourierDecayAlt.P.Sz3
