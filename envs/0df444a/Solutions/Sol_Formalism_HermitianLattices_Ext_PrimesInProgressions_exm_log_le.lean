-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_log_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:30.873507+00:00
-- url     : https://prove2.me/submissions/4ea63593-0ad0-46a0-837c-f8639983a3ef

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M T u : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) (hu0 : 0 ≤ u) (hu : u ≤ T + 1) :
    Real.log (M * (u + 2)) ≤ 2 * Real.log (M * T) := by
  have hM0 : 0 ≤ M := by linarith
  have hpos : 0 < M * (u + 2) := mul_pos (by linarith) (by linarith)
  have h3 : T + 3 ≤ M * T ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hM (sq_nonneg T),
      mul_nonneg (sub_nonneg.2 hT) (by linarith : (0:ℝ) ≤ T)]
  have h4 : M * (u + 2) ≤ M * (T + 3) := mul_le_mul_of_nonneg_left (by linarith) hM0
  have h5 : M * (T + 3) ≤ M * (M * T ^ 2) := mul_le_mul_of_nonneg_left h3 hM0
  have h2 : M * (u + 2) ≤ (M * T) ^ 2 := by nlinarith
  calc Real.log (M * (u + 2)) ≤ Real.log ((M * T) ^ 2) := Real.log_le_log hpos h2
    _ = 2 * Real.log (M * T) := by rw [Real.log_pow]; push_cast; ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
