-- Prove2me | solution 1 for Formalism.CountingSumsFrames.sizeBound_one_le_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:27:26.236123+00:00
-- url     : https://prove2.me/submissions/907f4cf0-8517-41cf-8ce7-4b42c71fd4f2

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSizeBoundsHolds
import Theorems.Thm_Formalism_CountingSumsFrames_pII0_one_le_mul

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
theorem _root_.solution (k r N Q c' Y : ℝ) (hk : 1 ≤ k) (hr : 1 ≤ r) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hc : 1 ≤ c') (hY : 1 ≤ Y) : 1 ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by
  have h1 : 1 ≤ k ^ 3 := one_le_pow₀ hk
  have h2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have h3 : 1 ≤ Q ^ 5 := one_le_pow₀ hQ
  exact pII0_one_le_mul (pII0_one_le_mul (pII0_one_le_mul (pII0_one_le_mul
    (pII0_one_le_mul h1 h2) hN) h3) hc) hY
end Formalism.CountingSumsFrames
