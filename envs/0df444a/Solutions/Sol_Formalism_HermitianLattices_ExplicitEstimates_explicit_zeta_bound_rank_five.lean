-- Prove2me | solution 1 for Formalism.HermitianLattices.ExplicitEstimates.explicit_zeta_bound_rank_five
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:04:35.222495+00:00
-- url     : https://prove2.me/submissions/22a6af65-7d3a-486e-a1e1-e99169fab826

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_IntegralMultipleNormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ColumnParametrizationOffDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ExplicitEstimates
open Finset
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (hookF)
namespace Formalism.HermitianLattices.ExplicitEstimates
theorem _root_.solution : AntitoneWeightLogBoundExplicit := by
  intro κ lam v logT logB logc muB mu hv hanti hB hc hmuB hmu
  have hW0 : 0 ≤ wt (plus lam) := by
    simp only [wt, plus]
    exact Finset.sum_nonneg (fun i _ => by have := hanti (Fin.le_last i); linarith)
  have hW : (0:ℝ) ≤ (wt (plus lam) : ℝ) := by exact_mod_cast hW0
  have hk : (0:ℝ) < (κ:ℝ) + 1 := by positivity
  have hv0 : (0:ℝ) < v := by linarith
  have hkey : Real.log ((κ:ℝ) + 1) + Real.log (4 * ((κ:ℝ) + 1) ^ 3 * v ^ 2)
      ≤ 4 * Real.log (((κ:ℝ) + 1) * v) := by
    have hpos2 : (4 * ((κ:ℝ) + 1) ^ 3 * v ^ 2) ≠ 0 := by positivity
    have e4 : 4 * Real.log (((κ:ℝ) + 1) * v) = Real.log ((((κ:ℝ) + 1) * v) ^ 4) := by
      rw [Real.log_pow]
      norm_num
    rw [← Real.log_mul hk.ne' hpos2, e4]
    apply Real.log_le_log (by positivity)
    have hv2 : (4:ℝ) ≤ v ^ 2 := by nlinarith
    have hP : (0:ℝ) ≤ ((κ:ℝ) + 1) ^ 4 * v ^ 2 := by positivity
    have e1 : ((κ:ℝ) + 1) * (4 * ((κ:ℝ) + 1) ^ 3 * v ^ 2) = 4 * (((κ:ℝ) + 1) ^ 4 * v ^ 2) := by ring
    have e2 : (((κ:ℝ) + 1) * v) ^ 4 = (((κ:ℝ) + 1) ^ 4 * v ^ 2) * v ^ 2 := by ring
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left hv2 hP]
  have h1 := mul_le_mul_of_nonneg_left hB hW
  have h2 := mul_le_mul_of_nonneg_left hkey hW
  linarith
end Formalism.HermitianLattices.ExplicitEstimates
