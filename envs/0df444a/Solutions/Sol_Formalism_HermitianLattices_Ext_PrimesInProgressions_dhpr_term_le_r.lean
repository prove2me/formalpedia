-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_term_le_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:16:27.18961+00:00
-- url     : https://prove2.me/submissions/333fd6a0-e2f7-45a5-b6a7-f2f5e513d528

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_coef_le

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
    (k n : ℕ) (σ : ℝ) :
    (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n ≤
      2 * (Real.log n) ^ (k + 1) * (zetaMul χ₁ n).re / (n : ℝ) ^ σ := by
  have hc := dhpr_coef_le χ₁ h1 n
  have hl := Real.log_natCast_nonneg n
  have h0 : 0 ≤ Real.log n ^ k / (n : ℝ) ^ σ :=
    div_nonneg (pow_nonneg hl k) (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  calc Real.log n ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n = (Real.log n ^ k / (n : ℝ) ^ σ) * (Λ n * dhprC χ₁ n) := by
        ring
    _ ≤ (Real.log n ^ k / (n : ℝ) ^ σ) * (2 * Real.log n * (zetaMul χ₁ n).re) := mul_le_mul_of_nonneg_left hc h0
    _ = 2 * Real.log n ^ (k + 1) * (zetaMul χ₁ n).re / (n : ℝ) ^ σ := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
