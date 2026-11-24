-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:54.538798+00:00
-- url     : https://prove2.me/submissions/69c969a8-a91a-456f-9e83-0973ac6208ac

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
theorem _root_.solution (S Ifull R Lf Bt Tp K D Sg : ℂ) (y : ℝ) (hy : 0 < y)
    (hS : S = (1 / (2 * Real.pi) : ℂ) * Ifull)
    (hrect : Bt - Tp + I * R - I * Lf = 2 * Real.pi * I * (K * y + D - Sg)) :
    S / y - K - D / y + Sg / y =
      (1 / (2 * Real.pi * y) : ℂ) * ((Ifull - R) + Lf + I * (Bt - Tp)) := by
  subst hS
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key : (Ifull - R) + Lf + I * (Bt - Tp) =
      Ifull - 2 * (Real.pi : ℂ) * (K * (y : ℂ) + D - Sg) := by
    linear_combination I * hrect + (-R + Lf + 2 * (Real.pi : ℂ) * (K * (y : ℂ) + D - Sg)) * I_sq
  rw [key]
  field_simp
  ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
