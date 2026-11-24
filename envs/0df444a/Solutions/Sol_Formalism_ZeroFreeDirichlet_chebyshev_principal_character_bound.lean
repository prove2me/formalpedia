-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.chebyshev_principal_character_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:29:58.795048+00:00
-- url     : https://prove2.me/submissions/adf444d9-b2bf-47f4-929e-028b499f6411

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SumVonMangoldtNotCoprimeLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_AbsZeroTermSecondDifferenceLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LeOfSecondDifferenceBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PsiChiBoundOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_smoothing_identity_real
import Theorems.Thm_Formalism_ZeroFreeDirichlet_exp_neg_sqrt_log_mem_unit_interval
import Theorems.Thm_Formalism_ZeroFreeDirichlet_abs_main_term_second_difference_le
import Theorems.Thm_Formalism_ZeroFreeDirichlet_exp_neg_sqrt_log_le_sq
import Theorems.Thm_Formalism_ZeroFreeDirichlet_le_of_second_difference_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_mul_le_of_log_bounds
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_weightedSum_sub_le
import Theorems.Thm_Formalism_ZeroFreeDirichlet_one_apply_natCast
import Theorems.Thm_Formalism_ZeroFreeDirichlet_sum_vonMangoldt_not_coprime_le


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
theorem _root_.solution {q : ℕ} [NeZero q] {cg Kg c₀ y : ℝ} (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1)
    (hcg : c₀ ≤ cg) (hKg : 0 ≤ Kg) (hy : 2 ≤ y)
    (hq : (q : ℝ) ≤ Real.exp (c₀ / 4 * Real.sqrt (Real.log y)))
    (hG : ∀ z : ℝ, y ≤ z → |Formalism.Gz z| ≤ Kg * z * Real.exp (-cg * Real.sqrt (Real.log z))) :
    ‖psiChi (1 : DirichletCharacter ℂ q) y - y‖ ≤
      (128 / c₀ ^ 2 + 2 + 4 * Kg) * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y))
        + 16 * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by
  obtain ⟨hh0, hh1⟩ := exp_neg_sqrt_log_mem_unit_interval (y := y) hc0
  set h := Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) with hh
  have hypos : 0 < y := by linarith
  have hyY : y ≤ y * (1 + h) := by nlinarith
  have hY0 : 0 ≤ y * (1 + h) := by positivity
  set f : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) with hf
  have hfb : ∀ n, ‖f n‖ ≤ Λ n := by
    intro n
    simp only [hf, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg, le_refl]
  have hS : ∀ x, weightedPartialSumUpTo f x = ((Formalism.Sz x : ℝ) : ℂ) := by
    intro x; simp only [weightedPartialSumUpTo, Formalism.Sz, hf]; push_cast; rfl
  set ψ₀ := ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n with hψ₀
  have hP : partialSumUpTo f y = ((ψ₀ : ℝ) : ℂ) := by
    simp only [partialSumUpTo, hf, hψ₀]; push_cast; rfl
  set nc := ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n * (if n.Coprime q then 0 else 1) with hnc
  have hpsi : psiChi (1 : DirichletCharacter ℂ q) y = ((ψ₀ - nc : ℝ) : ℂ) := by
    simp only [psiChi, one_apply_natCast, hψ₀, hnc]
    push_cast
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> simp

  have hD := norm_weightedSum_sub_le f hfb (show (1:ℝ) ≤ y by linarith) hyY
  rw [hS, hS, hP] at hD
  have hD' : |(y * Formalism.Sz (y * (1 + h)) - (y * (1 + h)) * Formalism.Sz y) - (y * (1 + h) - y) * ψ₀|
      ≤ (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h))) := by
    have e : ((y : ℂ) * ((Formalism.Sz (y * (1 + h)) : ℝ) : ℂ) - ((y * (1 + h) : ℝ) : ℂ) * ((Formalism.Sz y : ℝ) : ℂ))
        - ((y * (1 + h) - y : ℝ) : ℂ) * ((ψ₀ : ℝ) : ℂ)
        = (((y * Formalism.Sz (y * (1 + h)) - (y * (1 + h)) * Formalism.Sz y) - (y * (1 + h) - y) * ψ₀ : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs] at hD
    exact hD
  have hGY := hG (y * (1 + h)) hyY
  have hGy := hG y le_rfl
  set eY := Real.exp (-cg * Real.sqrt (Real.log (y * (1 + h))))
  set ey := Real.exp (-cg * Real.sqrt (Real.log y))
  have hid := chebyshev_smoothing_identity_real ψ₀ (Formalism.Sz (y * (1 + h))) (Formalism.Sz y) (Formalism.Gz (y * (1 + h))) (Formalism.Gz y) y h
    (by simp only [Formalism.Gz]; ring) (by simp only [Formalism.Gz]; ring)
  have hW := abs_main_term_second_difference_le (γ := Real.eulerMascheroniConstant) hypos hh0
  have hmain : y * h * |ψ₀ - y| ≤
      (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h)))
        + 2 * y ^ 2 * h ^ 2 + y * (Kg * (y * (1 + h)) * eY) + y * (1 + h) * (Kg * y * ey) := by
    rw [← abs_of_pos (show 0 < y * h by positivity), ← abs_mul, hid]
    have h1 : |y * Formalism.Gz (y * (1 + h)) - (y * (1 + h)) * Formalism.Gz y|
        ≤ y * (Kg * (y * (1 + h)) * eY) + y * (1 + h) * (Kg * y * ey) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hypos, abs_of_nonneg hY0]
      exact add_le_add (mul_le_mul_of_nonneg_left hGY hypos.le) (mul_le_mul_of_nonneg_left hGy hY0)
    have hsq : 0 ≤ y ^ 2 * h ^ 2 := by positivity
    calc _ ≤ |-((y * Formalism.Sz (y * (1 + h)) - (y * (1 + h)) * Formalism.Sz y) - (y * (1 + h) - y) * ψ₀)|
          + |y * ((y * (1 + h)) * Real.log (y * (1 + h))
            - (1 + Real.eulerMascheroniConstant) * (y * (1 + h)))
          - (y * (1 + h)) * (y * Real.log y - (1 + Real.eulerMascheroniConstant) * y) - y * h * y|
          + |y * Formalism.Gz (y * (1 + h)) - (y * (1 + h)) * Formalism.Gz y| := abs_add_three _ _ _
      _ ≤ _ := by rw [abs_neg]; linarith
  have hey := exp_neg_sqrt_log_le_sq (cs := cg) hc0.le hcg (show (1:ℝ) ≤ y by linarith) (le_refl y)
  have heY := exp_neg_sqrt_log_le_sq (cs := cg) hc0.le hcg (show (1:ℝ) ≤ y by linarith) hyY
  have hfin := le_of_second_difference_bound hy hc0 hc01 hKg hh (Real.exp_pos _).le (Real.exp_pos _).le hey heY hmain

  have hq0 : q ≠ 0 := NeZero.ne q
  have hnc1 := sum_vonMangoldt_not_coprime_le q hq0 ⌊y⌋₊
  rw [← hnc] at hnc1
  have hK : (Nat.log 2 ⌊y⌋₊ : ℝ) * Real.log 2 ≤ Real.log y := by
    have hfl : ⌊y⌋₊ ≠ 0 := by
      have : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith)
      omega
    have h2 : ((2 ^ Nat.log 2 ⌊y⌋₊ : ℕ) : ℝ) ≤ y := by
      have := Nat.pow_log_le_self 2 hfl
      calc ((2 ^ Nat.log 2 ⌊y⌋₊ : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast this
        _ ≤ y := Nat.floor_le hypos.le
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast h2
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hq0
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlq : Real.log q ≤ c₀ / 4 * Real.sqrt (Real.log y) := by
    have := Real.log_le_log (by linarith) hq
    rwa [Real.log_exp] at this
  have hncb := mul_le_of_log_bounds hy hc0 hc01 hK (by positivity) hlq0 hlq
  have hnc0 : 0 ≤ nc := Finset.sum_nonneg fun n _ =>
    mul_nonneg vonMangoldt_nonneg (by split_ifs <;> norm_num)
  rw [hpsi]
  have e : ((ψ₀ - nc : ℝ) : ℂ) - (y : ℂ) = (((ψ₀ - y) - nc : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  calc |(ψ₀ - y) - nc| ≤ |ψ₀ - y| + |nc| := abs_sub _ _
    _ ≤ _ := by rw [abs_of_nonneg hnc0]; linarith
end Formalism.ZeroFreeDirichlet
