-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mollM_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:39.400915+00:00
-- url     : https://prove2.me/submissions/5e481289-73a4-4c9b-9e66-64d879ebc591

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDetect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
open scoped ArithmeticFunction.Moebius
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 0 ≤ s.re) (Y : ℕ) :
    ‖∑ d ∈ Icc 1 Y, (((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)‖ ≤ Y := by
  refine le_trans (norm_sum_le _ _) ?_
  have h1 : ∀ d ∈ Icc 1 Y, ‖(((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)‖ ≤ 1 := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.1 hd).1
    rw [norm_mul, norm_mul]
    have hμ : ‖(((μ d : ℤ)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hχ : ‖χ (d : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hp : ‖(d : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      refine Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) ?_
      simp only [Complex.neg_re]
      linarith
    calc ‖(((μ d : ℤ)) : ℂ)‖ * ‖χ (d : ZMod q)‖ * ‖(d : ℂ) ^ (-s)‖ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  calc ∑ d ∈ Icc 1 Y, ‖(((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)‖ ≤ ∑ d ∈ Icc 1 Y, (1 : ℝ) :=
        Finset.sum_le_sum h1
    _ = Y := by simp
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
