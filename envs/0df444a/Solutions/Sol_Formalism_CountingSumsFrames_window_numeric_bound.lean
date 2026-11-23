-- Prove2me | solution 1 for Formalism.CountingSumsFrames.window_numeric_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:17.632959+00:00
-- url     : https://prove2.me/submissions/6877a709-804d-4131-bc9b-e3981c93a10d

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {R Y a P W w : ℝ} (hK : 3 ≤ R + 1) (hY : 1 ≤ Y) (hP : 0 < P) (hW0 : 0 ≤ W)
    (hW : (R + 1) * Y * W ≤ w * a) (hw0 : 0 ≤ w) (hw : w ≤ 5) (h3 : 3 * ((R + 1) ^ 2 * P * Y) ≤ a)
    (h9 : 9 * ((R + 1) * P) ≤ a) :
    0 < a / P - (R + 1) ∧
      R * ((a + W) / P - (a / P - (R + 1))) ≤ (w + 1) / Y * (a / P - (R + 1)) := by
  have hY0 : 0 < Y := by linarith
  have hKP : 0 < (R + 1) * P := by positivity
  have ha0 : 0 < a := by linarith
  have e0 : a / P - (R + 1) = (a - (R + 1) * P) / P := by field_simp
  have e1 : (a + W) / P - (a / P - (R + 1)) = (W + (R + 1) * P) / P := by field_simp; ring
  rw [e1, e0]
  refine ⟨div_pos (by linarith) hP, ?_⟩
  have hmain : R * (W + (R + 1) * P) * Y ≤ (w + 1) * (a - (R + 1) * P) := by
    have f1 : R * (W + (R + 1) * P) * Y ≤ (R + 1) * (W + (R + 1) * P) * Y := by
      gcongr; linarith
    have f2 : (R + 1) * (W + (R + 1) * P) * Y = (R + 1) * Y * W + (R + 1) ^ 2 * P * Y := by ring
    have f3 : (w + 1) * (8 / 9 * a) ≤ (w + 1) * (a - (R + 1) * P) := by gcongr; linarith
    have f4 : 0 ≤ (5 - w) * a := mul_nonneg (by linarith) ha0.le
    nlinarith
  have g1 : R * ((W + (R + 1) * P) / P) = R * (W + (R + 1) * P) / P := by ring
  have g2 : (w + 1) / Y * ((a - (R + 1) * P) / P) = (w + 1) * (a - (R + 1) * P) / Y / P := by ring
  rw [g1, g2]
  apply div_le_div_of_nonneg_right _ hP.le
  rw [le_div_iff₀ hY0]
  exact hmain
end Formalism.CountingSumsFrames
