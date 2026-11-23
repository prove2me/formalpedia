-- Prove2me | solution 1 for Formalism.CountingSumsFrames.sizeBound_fourth_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:56.865356+00:00
-- url     : https://prove2.me/submissions/ca4d0dd8-e96e-467a-b340-754e578a897d

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSizeBoundsHolds
import Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_first_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CountingSumsFrames
open Real
namespace Formalism.CountingSumsFrames
theorem _root_.solution (r N k Q c' Y : ℝ) (hr : 1 ≤ r) (hN : 1 ≤ N) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (hc : 1 ≤ c') (hY : 0 ≤ Y) : Y * k ^ 2 * Q ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by
  have h := sizeBound_first_term r N k Q 1 Y (by linarith) hN hk hQ (by norm_num) hY
  have h0 : 0 ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * Y := by positivity
  have h1 : Y * k ^ 2 * Q ≤ r ^ 2 * 1 * (Y * k ^ 2 * Q) := by
    have : 1 ≤ r ^ 2 := one_le_pow₀ hr
    have : 0 ≤ Y * k ^ 2 * Q := by positivity
    nlinarith
  have h2 : k ^ 3 * r ^ 2 * N * Q ^ 5 * 1 * Y ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by nlinarith
  linarith
end Formalism.CountingSumsFrames
