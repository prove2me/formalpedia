-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tail_kernel_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:49.73761+00:00
-- url     : https://prove2.me/submissions/219a3fe1-60c5-4d29-98f2-ddf1b15fd2a7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailKernel

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution (T : ℝ) (hT : 0 ≤ T) :
    ∫ u in (0 : ℝ)..T, 2 / (1 / 800 + u) = 2 * Real.log (1 + 800 * T) := by
  have hfun : (fun u : ℝ => 2 / (1 / 800 + u)) = fun u => 2 * (u + 1 / 800)⁻¹ := by
    funext u; rw [div_eq_mul_inv, add_comm]
  have hsh := intervalIntegral.integral_comp_add_right (a := 0) (b := T) (fun x : ℝ => x⁻¹) (1 / 800)
  rw [hfun, intervalIntegral.integral_const_mul, hsh,
    integral_inv_of_pos (by norm_num) (by linarith)]
  congr 2
  field_simp
  ring
end Formalism.HermitianLattices.Ext.BoxTail
