-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.one_add_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:39.868893+00:00
-- url     : https://prove2.me/submissions/c7c53684-f819-4b3d-b6c4-19111f4c7a5c

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (t : ℝ) (ht : |t| ≤ 1 / 4) : Real.exp (t - 2 / 3 * t ^ 2) ≤ 1 + t := by
  have h1 : |(-t)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg] at h
  have hpos : 0 < 1 + t := by have := abs_le.mp ht; linarith
  rw [← Real.le_log_iff_exp_le hpos]
  have h3 := (abs_le.mp h).1
  have hs0 : 0 ≤ |t| := abs_nonneg t
  have hs2 : |t| ^ 2 = t ^ 2 := sq_abs t
  have h4 : |t| ^ 4 / (1 - |t|) ≤ t ^ 2 / 12 := by
    rw [div_le_iff₀ (by linarith)]
    rw [← hs2]
    nlinarith [mul_nonneg hs0 hs0, pow_nonneg hs0 2, pow_nonneg hs0 3]
  have h5 : -(t ^ 2 / 4) ≤ t ^ 3 := by
    have : |t ^ 3| = |t| ^ 3 := abs_pow t 3
    have h6 := neg_abs_le (t ^ 3)
    rw [this] at h6
    rw [← hs2]
    nlinarith [mul_nonneg hs0 hs0]
  have e : 1 - -t = 1 + t := by ring
  rw [e] at h3
  norm_num at h3
  nlinarith
end Formalism.FourierDecayAlt.P.Sz4
