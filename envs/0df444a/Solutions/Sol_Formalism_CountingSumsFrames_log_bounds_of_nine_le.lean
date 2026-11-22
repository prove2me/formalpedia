-- Prove2me | solution 1 for Formalism.CountingSumsFrames.log_bounds_of_nine_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:43.722217+00:00
-- url     : https://prove2.me/submissions/452e9651-2317-45fd-807e-5f2903493ee0

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
theorem _root_.solution {pp a : ℝ} (hp : 9 ≤ pp) (ha : pp < a) :
    2 ≤ Real.log pp ∧ 1 < Real.logb pp a ∧ 2 ≤ Real.log a := by
  have h9 : (2 : ℝ) ≤ Real.log 9 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h1 := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith
  have hlp : Real.log 9 ≤ Real.log pp := Real.log_le_log (by norm_num) hp
  have hla : Real.log pp < Real.log a := Real.log_lt_log (by linarith) ha
  refine ⟨by linarith, ?_, by linarith⟩
  unfold Real.logb
  rw [one_lt_div (by linarith)]
  exact hla
end Formalism.CountingSumsFrames
