-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.log_one_add_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:57.076824+00:00
-- url     : https://prove2.me/submissions/3c417199-b7e7-42b1-98ed-d7d0a6c6333a

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz3
theorem _root_.solution (x : ℝ) (hx : |x| ≤ 1 / 4) : |Real.log (1 + x) - x| ≤ 2 / 3 * x ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -x) (by rw [abs_neg]; linarith) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
  have hy0 : 0 ≤ |x| := abs_nonneg x
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hB : |x| ^ (3 + 1) / (1 - |x|) ≤ x ^ 2 / 12 := by
    rw [div_le_iff₀ (by linarith)]
    have : |x| ^ (3 + 1) = x ^ 2 * |x| ^ 2 := by rw [← hx2]; ring
    rw [this]
    have h2 : |x| ^ 2 ≤ 1 / 16 := by nlinarith
    have h3 : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith
  have h' := abs_le.mp (h.trans hB)
  obtain ⟨hxl, hxu⟩ := abs_le.mp hx
  have h3 : 0 ≤ x ^ 2 := sq_nonneg x
  have hc1 : x ^ 3 ≤ x ^ 2 / 4 := by nlinarith
  have hc2 : -(x ^ 2 / 4) ≤ x ^ 3 := by nlinarith
  norm_num at h'
  rw [abs_le]
  constructor <;> nlinarith [h'.1, h'.2]
end Formalism.FourierDecayAlt.P.Sz3
