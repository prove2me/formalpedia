-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tail_kernel_norm_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:50.212599+00:00
-- url     : https://prove2.me/submissions/eb6116cf-2c8f-4bc5-b24d-84ba467a9a43

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
theorem _root_.solution (σ u : ℝ) (hσ1 : σ ≤ 1 - 1 / 800) :
    (1 / 800 + |u|) / 2 ≤ ‖(σ : ℂ) + (u : ℂ) * I - 1‖ := by
  have h1 := Complex.abs_re_le_norm ((σ : ℂ) + (u : ℂ) * I - 1)
  have h2 := Complex.abs_im_le_norm ((σ : ℂ) + (u : ℂ) * I - 1)
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.one_re, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add] at h1 h2
  have hre : 1 / 800 ≤ |σ - 1| := by
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  linarith
end Formalism.HermitianLattices.Ext.BoxTail
