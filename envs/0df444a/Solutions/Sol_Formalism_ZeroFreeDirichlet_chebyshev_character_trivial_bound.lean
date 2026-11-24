-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.chebyshev_character_trivial_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:44:12.988518+00:00
-- url     : https://prove2.me/submissions/5bbd1677-20a7-41a3-8412-afa9a71a187f

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (hx : 1 ≤ x) :
    ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤ x * (Real.log x + 1) := by
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : ‖psiChi χ x‖ ≤ x * Real.log x := by
    unfold psiChi
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log x := by
          apply Finset.sum_le_sum
          intro n hn
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          have hχ : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hnx : (n:ℝ) ≤ x :=
            le_trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2) (Nat.floor_le hx0)
          have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
          have hlog : Real.log n ≤ Real.log x := Real.log_le_log (Nat.cast_pos.mpr (by omega)) hnx
          have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
          calc ArithmeticFunction.vonMangoldt n * ‖χ (n : ZMod q)‖
              ≤ ArithmeticFunction.vonMangoldt n * 1 := mul_le_mul_of_nonneg_left hχ hΛ0
            _ ≤ Real.log x := by linarith
      _ = ((Finset.Icc 1 ⌊x⌋₊).card : ℝ) * Real.log x := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ x * Real.log x := by
          apply mul_le_mul_of_nonneg_right _ hlx
          rw [Nat.card_Icc, Nat.add_sub_cancel]
          exact Nat.floor_le hx0
  have h2 : ‖(if χ = 1 then (x : ℂ) else 0)‖ ≤ x := by
    split_ifs
    · rw [Complex.norm_real, Real.norm_of_nonneg hx0]
    · rw [norm_zero]
      exact hx0
  calc ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0)‖
      ≤ ‖psiChi χ x‖ + ‖(if χ = 1 then (x : ℂ) else 0)‖ := norm_sub_le _ _
    _ ≤ x * Real.log x + x := add_le_add h1 h2
    _ = x * (Real.log x + 1) := by ring
end Formalism.ZeroFreeDirichlet
