-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhPos_term_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:30:44.758428+00:00
-- url     : https://prove2.me/submissions/26411839-ff8c-4d85-a0b2-93f1b0a5b32f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_Positivity
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhPos_iter_logMul

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
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) (σ : ℝ) (n : ℕ) :
    term (logMul^[k] (↗ψ * ↗Λ)) (σ : ℂ) n =
      (((Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) : ℝ) : ℂ) * ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (Nat.cast_nonneg n)]
      simp
    have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    have hpos : ((n : ℝ) ^ σ) ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ).ne'
    rw [LSeries.term_of_ne_zero hn, dhPos_iter_logMul, hpow, hlog]
    simp only [Pi.mul_apply]
    push_cast
    field_simp
end Formalism.HermitianLattices.Ext.PrimesInProgressions
