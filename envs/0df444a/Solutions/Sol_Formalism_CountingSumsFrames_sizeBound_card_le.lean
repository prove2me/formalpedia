-- Prove2me | solution 1 for Formalism.CountingSumsFrames.sizeBound_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:55.993972+00:00
-- url     : https://prove2.me/submissions/3fc9a88e-cf3f-4ccb-9a39-8bb5783780e2

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
theorem _root_.solution (r N Nₛ k Q c' : ℝ) (hr : 2 ≤ r) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hc : 1 ≤ c')
    (hN0 : 0 ≤ N) (hNs2 : Nₛ ≤ 2 * N) : Nₛ ≤ r ^ 2 * N * k * c' * Q ^ 2 := by
  have hkcQ : 1 ≤ k * c' * Q ^ 2 := by
    have : 1 ≤ Q ^ 2 := one_le_pow₀ hQ
    have : 1 ≤ k * c' := by nlinarith
    nlinarith
  have h4 : 4 ≤ r ^ 2 := by nlinarith
  have e1 : 2 * N ≤ r ^ 2 * N := by nlinarith
  have e2 : r ^ 2 * N ≤ r ^ 2 * N * (k * c' * Q ^ 2) := by
    have : 0 ≤ r ^ 2 * N := by positivity
    nlinarith
  calc Nₛ ≤ 2 * N := hNs2
    _ ≤ r ^ 2 * N := e1
    _ ≤ r ^ 2 * N * (k * c' * Q ^ 2) := e2
    _ = r ^ 2 * N * k * c' * Q ^ 2 := by ring
end Formalism.CountingSumsFrames
