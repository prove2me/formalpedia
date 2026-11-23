-- Prove2me | solution 1 for Formalism.CountingSumsFrames.log_seg_le_four_logb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:54.266793+00:00
-- url     : https://prove2.me/submissions/906a0eae-2cda-4954-b03c-0b7a5d0fc4ac

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Theorems.Thm_Formalism_CountingSumsFrames_log_bounds_of_nine_le

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
theorem _root_.solution {p r : ℕ} {a : ℝ} (hp : (9 : ℝ) ≤ p) (hpa : (p : ℝ) < a) (hr : (r : ℝ) ≤ a) :
    0 ≤ lgSeg p a r ∧ lgSeg p a r ≤ 4 * Real.logb p a := by
  have hp1 : (1 : ℝ) < p := by linarith
  have ha0 : 0 < a := by linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  obtain ⟨_, hl1, _⟩ := log_bounds_of_nine_le hp hpa
  have h0 : 0 ≤ Real.logb p (8 * a + r) := Real.logb_nonneg hp1 (by linarith)
  have h1 : Real.logb p (8 * a + r) ≤ Real.logb p (p * a) := by
    apply Real.logb_le_logb_of_le hp1 (by linarith)
    nlinarith
  have h2 : Real.logb p (p * a) = 1 + Real.logb p a := by
    rw [Real.logb_mul (by linarith) ha0.ne', Real.logb_self_eq_one hp1]
  unfold lgSeg
  constructor <;> linarith
end Formalism.CountingSumsFrames
