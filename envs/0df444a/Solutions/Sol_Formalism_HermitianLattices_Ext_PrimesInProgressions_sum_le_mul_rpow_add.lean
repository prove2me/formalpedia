-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.sum_le_mul_rpow_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:30.500396+00:00
-- url     : https://prove2.me/submissions/184089cb-88a6-4cb3-9b4c-9f7dcdef0ed0

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
theorem _root_.solution (AL AW C X Y W : ℝ) (hC4 : 4 ≤ C) (hCL : AL ≤ C) (hCW : AW ≤ C) (hX : 1 ≤ X)
    (hY : 0 ≤ Y) (hW : 0 ≤ W) : AL * (X ^ 4 * Y) + AW * W ≤ C * (X ^ C * Y + W) := by
  have hX0 : 0 ≤ X := by linarith
  have hC0 : 0 ≤ C := by linarith
  have h4 : X ^ 4 ≤ X ^ C := by
    have h := Real.rpow_le_rpow_of_exponent_le hX hC4
    have e : X ^ (4 : ℝ) = X ^ (4 : ℕ) := by exact_mod_cast Real.rpow_natCast X 4
    rwa [e] at h
  have h1 := mul_le_mul_of_nonneg_right hCL (mul_nonneg (pow_nonneg hX0 4) hY)
  have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hY) hC0
  have h3 := mul_le_mul_of_nonneg_right hCW hW
  nlinarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
