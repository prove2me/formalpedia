-- Prove2me | solution 1 for Formalism.CountingSumsFrames.sizeBound_first_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:33.320658+00:00
-- url     : https://prove2.me/submissions/7fb1818b-33f2-4fdb-a74e-d3c048c405cf

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSizeBoundsHolds

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
theorem _root_.solution (r N k Q c' Y : ℝ) (hr : 0 ≤ r) (hN : 1 ≤ N) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (hc : 0 ≤ c') (hY : 0 ≤ Y) :
    r ^ 2 * c' * (Y * k ^ 2 * Q) ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by
  have h0 : 0 ≤ r ^ 2 * c' * Y * k ^ 2 * Q := by positivity
  have h1 : 1 ≤ k * N * Q ^ 4 := by
    have : 1 ≤ Q ^ 4 := one_le_pow₀ hQ
    have : 1 ≤ k * N := by nlinarith
    nlinarith
  calc r ^ 2 * c' * (Y * k ^ 2 * Q) = (r ^ 2 * c' * Y * k ^ 2 * Q) * 1 := by ring
    _ ≤ (r ^ 2 * c' * Y * k ^ 2 * Q) * (k * N * Q ^ 4) := mul_le_mul_of_nonneg_left h1 h0
    _ = k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by ring
end Formalism.CountingSumsFrames
