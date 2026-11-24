-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.chebyshev_character_nonprincipal_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:29:58.048864+00:00
-- url     : https://prove2.me/submissions/4d8a3304-b9e0-48c0-84a3-bb67eec84a48

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SumVonMangoldtNotCoprimeLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_AbsZeroTermSecondDifferenceLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LeOfSecondDifferenceBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PsiChiBoundOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_smoothing_identity_complex
import Theorems.Thm_Formalism_ZeroFreeDirichlet_exp_neg_sqrt_log_mem_unit_interval
import Theorems.Thm_Formalism_ZeroFreeDirichlet_abs_zero_term_second_difference_le
import Theorems.Thm_Formalism_ZeroFreeDirichlet_exp_neg_sqrt_log_le_sq
import Theorems.Thm_Formalism_ZeroFreeDirichlet_le_of_second_difference_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_weightedSum_sub_le


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
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c₁ : ℝ}
    (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 20) (B : Finset ℝ) (hB : ExcZeros c₁ χ B)
    {cs Cs c₀ y : ℝ} (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1) (hcs : c₀ ≤ cs) (hCs : 0 ≤ Cs) (hy : 2 ≤ y)
    (hE : ∀ z : ℝ, y ≤ z →
      ‖Schi χ z - negLD χ 1 * z + ∑ β ∈ B, (z : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤
        Cs * z * Real.exp (-cs * Real.sqrt (Real.log z))) :
    ‖psiChi χ y + ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
      (128 / c₀ ^ 2 + 2 + 4 * Cs) * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by
  obtain ⟨hh0, hh1⟩ := exp_neg_sqrt_log_mem_unit_interval (y := y) hc0
  set h := Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) with hh
  have hypos : 0 < y := by linarith
  have hyY : y ≤ y * (1 + h) := by nlinarith
  have hY0 : 0 ≤ y * (1 + h) := by positivity

  have hβ : ∀ β ∈ B, 1 / 2 ≤ β ∧ β < 1 := by
    intro β hβB
    obtain ⟨_, hreg, hzero, _⟩ := hB.2.1 β hβB
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
    simp only [InRegion, Complex.ofReal_im, abs_zero, zero_add, Complex.ofReal_re] at hreg
    have hl : Real.log 2 ≤ Real.log ((q : ℝ) * 2) := Real.log_le_log (by norm_num) (by linarith)
    have hl2 := Real.log_two_gt_d9
    have hlpos : 0 < Real.log ((q : ℝ) * 2) := by linarith
    have hfrac : c₁ / Real.log ((q : ℝ) * 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ hlpos]; linarith
    refine ⟨by linarith, ?_⟩
    by_contra hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by simpa using not_lt.1 hge) hzero
  set f : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) with hf
  have hfb : ∀ n, ‖f n‖ ≤ Λ n := by
    intro n
    simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _)
  have hS : ∀ x, Schi χ x = weightedPartialSumUpTo f x := fun x => rfl
  have hP : psiChi χ y = partialSumUpTo f y := rfl
  have hD := norm_weightedSum_sub_le f hfb (show (1:ℝ) ≤ y by linarith) hyY
  set MY := ∑ β ∈ B, (((y * (1 + h) : ℝ) : ℂ)) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)) with hMY
  set My := ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)) with hMy
  set Z := ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / (β : ℂ) with hZ
  have hid := chebyshev_smoothing_identity_complex (psiChi χ y) Z (Schi χ (y * (1 + h))) (Schi χ y) MY My (negLD χ 1) y h

  have hM : ‖((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z‖ ≤
      2 * y ^ 2 * h ^ 2 := by
    have e : ((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z
        = ∑ β ∈ B, (((y * (1 + h) * (y ^ β / (β * (β - 1))) - y * ((y * (1 + h)) ^ β / (β * (β - 1)))
            + y * h * (y ^ β / β) : ℝ)) : ℂ) := by
      rw [hMY, hMy, hZ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro β _
      rw [← Complex.ofReal_cpow hypos.le, ← Complex.ofReal_cpow hY0]
      push_cast; ring
    rw [e]
    calc _ ≤ ∑ β ∈ B, ‖(((y * (1 + h) * (y ^ β / (β * (β - 1)))
              - y * ((y * (1 + h)) ^ β / (β * (β - 1))) + y * h * (y ^ β / β) : ℝ)) : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ β ∈ B, 2 * y ^ 2 * h ^ 2 := by
          apply Finset.sum_le_sum
          intro β hβB
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact abs_zero_term_second_difference_le (by linarith) hh0 hh1 (hβ β hβB).1 (hβ β hβB).2
      _ = (B.card : ℝ) * (2 * y ^ 2 * h ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (2 * y ^ 2 * h ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hB.1
      _ = 2 * y ^ 2 * h ^ 2 := one_mul _
  have hEY := hE (y * (1 + h)) hyY
  have hEy := hE y le_rfl
  set eY := Real.exp (-cs * Real.sqrt (Real.log (y * (1 + h))))
  set ey := Real.exp (-cs * Real.sqrt (Real.log y))
  have hmain : y * h * ‖psiChi χ y + Z‖ ≤
      (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h)))
        + 2 * y ^ 2 * h ^ 2 + y * (Cs * (y * (1 + h)) * eY) + y * (1 + h) * (Cs * y * ey) := by
    have hn : ‖((y * h : ℝ) : ℂ) * (psiChi χ y + Z)‖ = y * h * ‖psiChi χ y + Z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [← hn, hid]
    have hD' : ‖((y : ℂ) * Schi χ (y * (1 + h)) - ((y * (1 + h) : ℝ) : ℂ) * Schi χ y)
        - ((y * (1 + h) - y : ℝ) : ℂ) * psiChi χ y‖
        ≤ (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h))) := by
      rw [hS, hS, hP]; exact hD
    have h1 : ‖(y : ℂ) * (Schi χ (y * (1 + h)) - negLD χ 1 * ((y * (1 + h) : ℝ) : ℂ) + MY)‖
        ≤ y * (Cs * (y * (1 + h)) * eY) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos]
      exact mul_le_mul_of_nonneg_left hEY hypos.le
    have h2 : ‖((y * (1 + h) : ℝ) : ℂ) * (Schi χ y - negLD χ 1 * (y : ℂ) + My)‖
        ≤ y * (1 + h) * (Cs * y * ey) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hY0]
      exact mul_le_mul_of_nonneg_left hEy hY0
    calc _ ≤ ‖-(((y : ℂ) * Schi χ (y * (1 + h)) - ((y * (1 + h) : ℝ) : ℂ) * Schi χ y)
              - ((y * (1 + h) - y : ℝ) : ℂ) * psiChi χ y)
            + (((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z)‖
          + ‖(y : ℂ) * (Schi χ (y * (1 + h)) - negLD χ 1 * ((y * (1 + h) : ℝ) : ℂ) + MY)
            - ((y * (1 + h) : ℝ) : ℂ) * (Schi χ y - negLD χ 1 * (y : ℂ) + My)‖ := norm_add_le _ _
      _ ≤ (‖((y : ℂ) * Schi χ (y * (1 + h)) - ((y * (1 + h) : ℝ) : ℂ) * Schi χ y)
              - ((y * (1 + h) - y : ℝ) : ℂ) * psiChi χ y‖
            + ‖((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z‖)
          + (‖(y : ℂ) * (Schi χ (y * (1 + h)) - negLD χ 1 * ((y * (1 + h) : ℝ) : ℂ) + MY)‖
            + ‖((y * (1 + h) : ℝ) : ℂ) * (Schi χ y - negLD χ 1 * (y : ℂ) + My)‖) := by
          gcongr
          · exact (norm_add_le _ _).trans (by rw [norm_neg])
          · exact norm_sub_le _ _
      _ ≤ _ := by linarith
  have hey := exp_neg_sqrt_log_le_sq (cs := cs) hc0.le hcs (show (1:ℝ) ≤ y by linarith) (le_refl y)
  have heY := exp_neg_sqrt_log_le_sq (cs := cs) hc0.le hcs (show (1:ℝ) ≤ y by linarith) hyY
  exact le_of_second_difference_bound hy hc0 hc01 hCs hh (Real.exp_pos _).le (Real.exp_pos _).le hey heY hmain
end Formalism.ZeroFreeDirichlet
