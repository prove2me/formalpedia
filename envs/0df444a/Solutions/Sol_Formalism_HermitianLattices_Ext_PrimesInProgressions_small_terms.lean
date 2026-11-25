-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.small_terms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:36:59.986902+00:00
-- url     : https://prove2.me/submissions/a84ade16-61a5-4ae5-80aa-0b20f9e57ce2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {c₃ c₁ L l η φ : ℝ} (hc₃ : 0 ≤ c₃) (hc₁ : 0 < c₁) (hL : 16 * l ≤ L) (hL1 : 1 ≤ L)
    (hη : c₁ * Real.exp (-l) ≤ η) (hφ0 : 0 < φ) (hφ : φ ≤ Real.exp l) :
    44 * Real.exp (L / 2) * L ≤
      5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) * (Real.exp L * η / (2 * L) / φ) := by
  have hL0 : 0 < L := by linarith
  have hsq : Real.sqrt (c₃ * L) ≤ 2 * c₃ + L / 8 := by
    calc Real.sqrt (c₃ * L) ≤ Real.sqrt ((2 * c₃ + L / 8) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (2 * c₃ - L / 8)])
      _ = 2 * c₃ + L / 8 := Real.sqrt_sq (by positivity)
  have hexpL : L ^ 2 ≤ 64 * Real.exp (L / 4) := by
    have h := Real.quadratic_le_exp_of_nonneg (x := L / 4) (by positivity)
    nlinarith
  have hsplit : Real.exp (3 * L / 4) = Real.exp (L / 2) * Real.exp (L / 4) := by
    rw [← Real.exp_add]
    ring_nf
  have key : 2816 * Real.exp (2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l) / L =
      5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) *
        (Real.exp L * (c₁ * Real.exp (-l)) / (2 * L) / Real.exp l) := by
    have e : Real.exp (2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l) =
        Real.exp (2 * c₃) * Real.exp (-Real.sqrt (c₃ * L)) * Real.exp L * Real.exp (-l) / Real.exp l := by
      rw [show 2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l = 2 * c₃ + -Real.sqrt (c₃ * L) + L + -l - l by ring,
        Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_add]
    rw [e]
    field_simp
    ring
  calc 44 * Real.exp (L / 2) * L ≤ 2816 * Real.exp (3 * L / 4) / L := by
        rw [le_div_iff₀ hL0, hsplit]
        have hp := Real.exp_pos (L / 2)
        nlinarith
    _ ≤ 2816 * Real.exp (2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l) / L := by
        apply div_le_div_of_nonneg_right _ hL0.le
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        linarith
    _ = 5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) *
        (Real.exp L * (c₁ * Real.exp (-l)) / (2 * L) / Real.exp l) := key
    _ ≤ 5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) * (Real.exp L * η / (2 * L) / φ) := by
        gcongr
        exact div_nonneg (mul_nonneg (Real.exp_pos L).le (le_trans (mul_pos hc₁ (Real.exp_pos _)).le hη)) (by positivity)
end Formalism.HermitianLattices.Ext.PrimesInProgressions
