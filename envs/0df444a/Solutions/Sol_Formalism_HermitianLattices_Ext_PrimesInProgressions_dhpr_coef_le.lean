-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_coef_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:03:51.341045+00:00
-- url     : https://prove2.me/submissions/c08bacc7-d48a-47c5-9b83-3ec3d1fce263

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_r_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_zetaMul_prime_pow

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
    (n : ℕ) : Λ n * dhprC χ₁ n ≤ 2 * Real.log n * (zetaMul χ₁ n).re := by
  have hr0 := dhpr_r_nonneg χ₁ h1 n
  have hl := Real.log_natCast_nonneg n
  by_cases hΛ : Λ n = 0
  · rw [hΛ, zero_mul]
    exact mul_nonneg (mul_nonneg (by norm_num) hl) hr0
  obtain ⟨p, a, hp', ha, rfl⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
  have hp : p.Prime := Nat.prime_iff.mpr hp'
  have ha0 : a ≠ 0 := Nat.pos_iff_ne_zero.mp ha
  have hΛp : Λ (p ^ a) = Real.log p := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow ha0, ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog : Real.log ((p ^ a : ℕ) : ℝ) = a * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]
  have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha

  have key : dhprC χ₁ (p ^ a) ≤ 2 * (zetaMul χ₁ (p ^ a)).re := by
    unfold dhprC
    rw [dhpr_zetaMul_prime_pow χ₁ hp a]
    by_cases hu : IsUnit (p : ZMod M)
    · have hua : IsUnit ((p ^ a : ℕ) : ZMod M) := by rw [Nat.cast_pow]; exact hu.pow a
      have h2 : χ₁ (p : ZMod M) ^ 2 = 1 := by
        have e := congrArg (fun ψ : DirichletCharacter ℂ M => ψ hu.unit) h1
        simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at e
        simpa using e
      have h3 : χ₁ (p : ZMod M) = 1 ∨ χ₁ (p : ZMod M) = -1 := mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)
      rw [MulChar.one_apply hua, Nat.cast_pow, map_pow]
      rcases h3 with h3 | h3
      · rw [h3]
        simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        simp
        linarith
      · rw [h3]
        have hsum : ∀ b : ℕ, 2 * ∑ i ∈ range (b + 1), ((-1 : ℂ)) ^ i = 1 + (-1) ^ b := by
          intro b
          induction b with
          | zero => norm_num
          | succ b ih =>
            rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
            ring
        have hre := congrArg Complex.re (hsum a)
        simp only [Complex.add_re, Complex.one_re] at hre
        have h2re : (2 * ∑ i ∈ range (a + 1), ((-1 : ℂ)) ^ i).re = 2 * (∑ i ∈ range (a + 1), ((-1 : ℂ)) ^ i).re := by
          simp [Complex.mul_re] <;> split_ifs <;> simp
        rw [h2re] at hre
        simp only [Complex.one_re]
        linarith
    · have hua : ¬ IsUnit ((p ^ a : ℕ) : ZMod M) := by
        rw [Nat.cast_pow]
        exact fun h => hu ((isUnit_pow_iff ha0).mp h)
      rw [MulChar.map_nonunit _ hua, MulChar.map_nonunit _ hua]
      have := (Complex.nonneg_iff.mp (DirichletCharacter.zetaMul_nonneg h1 (p ^ a))).1
      rw [dhpr_zetaMul_prime_pow χ₁ hp a] at this
      simp only [Complex.zero_re, add_zero]
      linarith
  rw [hΛp, hlog]
  calc Real.log p * dhprC χ₁ (p ^ a) ≤ Real.log p * (2 * (zetaMul χ₁ (p ^ a)).re) :=
        mul_le_mul_of_nonneg_left key hlp
    _ ≤ 2 * (a * Real.log p) * (zetaMul χ₁ (p ^ a)).re := by
        have hrr := dhpr_r_nonneg χ₁ h1 (p ^ a)
        nlinarith [mul_nonneg hlp hrr]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
