-- Prove2me | solution 1 for Formalism.CountingSumsFrames.sizeBound_count_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:56.612824+00:00
-- url     : https://prove2.me/submissions/aa8c9381-9f76-4ef7-b2b1-0b4945a84c0b

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
theorem _root_.solution (r N N₁ Nₛ : ℝ) (hrN1 : 2 ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N) (hNs1 : Nₛ ≤ N₁) :
    Nₛ * (N₁ + 1) ≤ 2 * r * N := by
  rcases le_or_gt 0 Nₛ with hs | hs
  · have : Nₛ * (N₁ + 1) ≤ N₁ * (N₁ + 1) := mul_le_mul_of_nonneg_right hNs1 (by linarith)
    nlinarith
  · have : Nₛ * (N₁ + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs.le (by linarith)
    nlinarith
end Formalism.CountingSumsFrames
