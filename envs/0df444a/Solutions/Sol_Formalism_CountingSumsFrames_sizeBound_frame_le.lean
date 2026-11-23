-- Prove2me | solution 1 for Formalism.CountingSumsFrames.sizeBound_frame_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:56.829806+00:00
-- url     : https://prove2.me/submissions/e386edae-7711-44ed-83f4-adf682fb7524

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
theorem _root_.solution (r N N₁ Nₛ k : ℝ) (hr : 2 ≤ r) (hrN1 : r ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N)
    (hk8 : 8 ≤ k) (hN0 : 0 ≤ N) (hNs1 : Nₛ ≤ N₁) (hNs2 : Nₛ ≤ 2 * N) :
    Nₛ * (N₁ + r * k) ≤ 2 * r ^ 2 * N * k := by
  have hpos : 0 ≤ N₁ + r * k := by nlinarith
  have hrk : 0 ≤ r * N * k := by positivity
  rcases le_or_gt 0 Nₛ with hs | hs
  · have e1 : Nₛ * N₁ ≤ N₁ ^ 2 := by nlinarith
    have e2 : r * N ≤ r ^ 2 * N * k := by nlinarith
    have e3 : Nₛ * (r * k) ≤ 2 * N * (r * k) := by
      apply mul_le_mul_of_nonneg_right hNs2; positivity
    have e4 : 2 * N * (r * k) ≤ r ^ 2 * N * k := by nlinarith
    nlinarith
  · have : Nₛ * (N₁ + r * k) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs.le hpos
    have : 0 ≤ 2 * r ^ 2 * N * k := by positivity
    linarith
end Formalism.CountingSumsFrames
