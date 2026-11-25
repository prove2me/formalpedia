-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_term_le_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:17:45.777023+00:00
-- url     : https://prove2.me/submissions/1ad55886-7735-4874-9ba9-f40986a1008a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_C_bounds

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
open scoped LSeries.notation ComplexOrder
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1)
    (k n : ℕ) {σ : ℝ} (hσ : 1 ≤ σ) :
    (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n ≤ 2 * (Real.log n) ^ k * (Λ n / n) := by
  have hC := dhpr_C_bounds χ₁ h1 n
  have hl := Real.log_natCast_nonneg n
  have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  by_cases hn : n = 0
  · subst hn
    simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ σ := by
    have := Real.rpow_le_rpow_of_exponent_le hn1 hσ
    rwa [Real.rpow_one] at this
  have hd : Λ n / (n : ℝ) ^ σ ≤ Λ n / n := div_le_div_of_nonneg_left hΛ (by linarith) hpow
  have h0 : 0 ≤ Real.log n ^ k * (Λ n / n) := mul_nonneg (pow_nonneg hl k) (div_nonneg hΛ (Nat.cast_nonneg n))
  calc Real.log n ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n ≤ Real.log n ^ k * (Λ n / n) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd (pow_nonneg hl k)) hC.2 hC.1 h0
    _ = 2 * Real.log n ^ k * (Λ n / n) := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
