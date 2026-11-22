-- Prove2me | solution 1 for Formalism.CountingSumsFrames.derived_parameter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:59.237065+00:00
-- url     : https://prove2.me/submissions/763234a2-74d5-449d-bee2-283ab345fde2

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
theorem _root_.solution {K Y a b' Q pp : ℝ} (hY : 1 ≤ Y) (hp : K ^ 2 * Y ^ 2 ≤ pp) (h4 : K ^ 3 * Q * Y ≤ b')
    (hba : b' ≤ a) (h6 : pp < a / b') (hK : 3 ≤ K) (hQ : 1 ≤ Q) (hb0 : 0 < b') :
    9 ≤ pp ∧ 27 ≤ b' ∧ pp * b' < a ∧ 243 < a ∧ pp < a ∧ 9 * (K * Q) ≤ a ∧ K ≤ a ∧
      9 * (K * Q * Y) ≤ a ∧ 3 * (K ^ 2 * Q * Y) ≤ a := by
  have hK2 : (9 : ℝ) ≤ K ^ 2 := by
    calc (9 : ℝ) = 3 ^ 2 := by norm_num
      _ ≤ K ^ 2 := by gcongr
  have hK3 : (27 : ℝ) ≤ K ^ 3 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ K ^ 3 := by gcongr
  have hK0 : 0 < K := by linarith
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hp9 : 9 ≤ pp := by
    calc (9 : ℝ) = 9 * 1 := by norm_num
      _ ≤ K ^ 2 * Y ^ 2 := by gcongr
      _ ≤ pp := hp
  have hb27 : 27 ≤ b' := by
    calc (27 : ℝ) = 27 * 1 * 1 := by norm_num
      _ ≤ K ^ 3 * Q * Y := by gcongr
      _ ≤ b' := h4
  have hpb : pp * b' < a := (lt_div_iff₀ hb0).mp h6
  have h243 : (243 : ℝ) ≤ pp * b' := by
    calc (243 : ℝ) = 9 * 27 := by norm_num
      _ ≤ pp * b' := by gcongr
  have hppa : pp ≤ pp * b' := le_mul_of_one_le_right (by linarith) (by linarith)
  have hKQY : 9 * (K * Q * Y) ≤ a := by
    calc 9 * (K * Q * Y) ≤ K ^ 2 * (K * Q * Y) := by gcongr
      _ = K ^ 3 * Q * Y := by ring
      _ ≤ a := by linarith
  have hKQ : K * Q ≤ K * Q * Y := le_mul_of_one_le_right (by positivity) hY
  have hKK : K ≤ K * Q := le_mul_of_one_le_right hK0.le hQ
  have hK2QY : 3 * (K ^ 2 * Q * Y) ≤ a := by
    calc 3 * (K ^ 2 * Q * Y) ≤ K * (K ^ 2 * Q * Y) := by gcongr
      _ = K ^ 3 * Q * Y := by ring
      _ ≤ a := by linarith
  have hKQ0 : 0 < K * Q := by positivity
  exact ⟨hp9, hb27, hpb, by linarith, by linarith, by linarith, by linarith, hKQY, hK2QY⟩
end Formalism.CountingSumsFrames
