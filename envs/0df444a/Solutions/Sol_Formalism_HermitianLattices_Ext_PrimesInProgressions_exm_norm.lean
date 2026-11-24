-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:42.179147+00:00
-- url     : https://prove2.me/submissions/2164e041-5cf1-41c5-b4a0-021eaa3a53f2

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
theorem _root_.solution (Ifull R Lf Bt Tp : ℂ) (y a b c d : ℝ) (hy : 0 < y)
    (ha : ‖Ifull - R‖ ≤ a) (hb : ‖Lf‖ ≤ b) (hc : ‖Bt‖ ≤ c) (hd : ‖Tp‖ ≤ d) :
    ‖(1 / (2 * Real.pi * y) : ℂ) * ((Ifull - R) + Lf + I * (Bt - Tp))‖ ≤
      1 / (2 * Real.pi * y) * (a + b + (c + d)) := by
  have hpos : 0 < 2 * Real.pi * y := mul_pos (mul_pos two_pos Real.pi_pos) hy
  have hk : (1 / (2 * Real.pi * y) : ℂ) = ((1 / (2 * Real.pi * y) : ℝ) : ℂ) := by
    norm_cast
  rw [hk, norm_mul, Complex.norm_real, Real.norm_of_nonneg (one_div_pos.2 hpos).le]
  apply mul_le_mul_of_nonneg_left _ (one_div_pos.2 hpos).le
  have h1 := norm_add_le (Ifull - R) Lf
  have h2 : ‖I * (Bt - Tp)‖ = ‖Bt - Tp‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have h3 := norm_sub_le Bt Tp
  have h4 := norm_add_le (Ifull - R + Lf) (I * (Bt - Tp))
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
