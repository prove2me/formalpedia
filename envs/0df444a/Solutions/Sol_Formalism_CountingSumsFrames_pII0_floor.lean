-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pII0_floor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:23.860933+00:00
-- url     : https://prove2.me/submissions/af69e2be-01ee-4d70-bf72-c527a5401f11

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
theorem _root_.solution (L Y k Q a B : ℝ) (hQ0 : 0 < Q) (ha : 0 ≤ a) (hYk100 : 100 ≤ Y * k ^ 2)
    (h : (L + 1) * (Y * k ^ 2 * Q) ≤ a) (hB : a / Q ≤ B) :
    L ≤ ((⌊B / (Y * k ^ 2)⌋ : ℤ) : ℝ) ∧ ((⌊B / (Y * k ^ 2)⌋ : ℤ) : ℝ) ≤ B / 100 := by
  have hW : 0 < Y * k ^ 2 := by linarith
  have h1 : (L + 1) * (Y * k ^ 2) ≤ a / Q := by
    rw [le_div_iff₀ hQ0]; linarith [show (L + 1) * (Y * k ^ 2) * Q = (L + 1) * (Y * k ^ 2 * Q) by ring]
  have h2 : L + 1 ≤ B / (Y * k ^ 2) := by
    rw [le_div_iff₀ hW]; linarith
  have hB0 : 0 ≤ B := le_trans (div_nonneg ha hQ0.le) hB
  constructor
  · have := Int.sub_one_lt_floor (B / (Y * k ^ 2))
    linarith
  · have h3 : B / (Y * k ^ 2) ≤ B / 100 := by
      gcongr
    exact le_trans (Int.floor_le _) h3
end Formalism.CountingSumsFrames
