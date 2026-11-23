-- Prove2me | solution 1 for Formalism.CountingSumsFrames.sizeBound_second_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:56.875872+00:00
-- url     : https://prove2.me/submissions/96d8d280-7f88-4261-8535-f8925aa07176

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
theorem _root_.solution (r N N₁ k Q c' Y c₀ : ℝ) (hr : 1 ≤ r) (hN : 1 ≤ N) (hk0 : 0 ≤ k) (hQ : 1 ≤ Q)
    (hY : 0 ≤ Y) (hNk : N₁ + r ≤ k) (hc00 : 0 ≤ c₀) (hc0 : c₀ ≤ c') :
    (N₁ + r) * c₀ * (Y * k ^ 2 * Q) ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by
  have hW : 0 ≤ Y * k ^ 2 * Q := by positivity
  have e1 : (N₁ + r) * c₀ ≤ k * c' := by
    calc (N₁ + r) * c₀ ≤ k * c₀ := mul_le_mul_of_nonneg_right hNk hc00
      _ ≤ k * c' := mul_le_mul_of_nonneg_left hc0 hk0
  have hc : 0 ≤ c' := le_trans hc00 hc0
  have h1 : 1 ≤ r ^ 2 * N * Q ^ 4 := by
    have : 1 ≤ Q ^ 4 := one_le_pow₀ hQ
    have : 1 ≤ r ^ 2 := one_le_pow₀ hr
    have : 1 ≤ r ^ 2 * N := by nlinarith
    nlinarith
  have h0 : 0 ≤ k ^ 3 * c' * Y * Q := by positivity
  calc (N₁ + r) * c₀ * (Y * k ^ 2 * Q) ≤ k * c' * (Y * k ^ 2 * Q) := mul_le_mul_of_nonneg_right e1 hW
    _ = (k ^ 3 * c' * Y * Q) * 1 := by ring
    _ ≤ (k ^ 3 * c' * Y * Q) * (r ^ 2 * N * Q ^ 4) := mul_le_mul_of_nonneg_left h1 h0
    _ = k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by ring
end Formalism.CountingSumsFrames
