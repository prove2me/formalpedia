-- Prove2me | solution 1 for Deduction.mertens_upper_sum_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:26.348888+00:00
-- url     : https://prove2.me/submissions/4e5e59af-c68c-4c1e-9852-76820b7d8395

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mertensUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n ≤ N * Real.log N - N + 1 + Real.log N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _)]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : Real.log ((N : ℝ) / (N + 1)) ≤ (N : ℝ) / (N + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hN'.ne' (by positivity)] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ N + 1 by positivity)
    have h3 : ((N : ℝ) + 1) * ((N : ℝ) / (N + 1) - 1) = -1 := by field_simp; ring
    rw [h3] at h2
    push_cast
    nlinarith
end Deduction
