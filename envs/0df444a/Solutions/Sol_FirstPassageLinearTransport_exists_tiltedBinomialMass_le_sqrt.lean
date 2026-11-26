-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_tiltedBinomialMass_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:51.274376+00:00
-- url     : https://prove2.me/submissions/c256cff1-41e3-4940-ba12-226129ea7aa1

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_exists_tiltedBinomialMass_le_sqrt_of_quarter
import Theorems.Thm_FirstPassageLinearTransport_tiltedBinomialMass_nonneg
import Theorems.Thm_FirstPassageLinearTransport_tiltedBinomialMass_le_one
import Theorems.Thm_FirstPassageLinearTransport_maximizer_is_in_quarter_window
import Theorems.Thm_FirstPassageLinearTransport_exists_tiltedBinomialMass_maximizer
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p : ℝ} (hpHalf : 1 / 2 < p) (hpTwoThird : p < 2 / 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 0 < n →
      tiltedBinomialMass p n k ≤ C / Real.sqrt n := by
  have hp₀ : 0 < p := by linarith
  have hp₁ : p < 1 := by linarith
  obtain ⟨C₀, hC₀, hcentral⟩ :=
    exists_tiltedBinomialMass_le_sqrt_of_quarter hp₀ hp₁
  refine ⟨max C₀ 3, lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
  intro n k hn
  by_cases hnLarge : 9 ≤ n
  · obtain ⟨k₀, hk₀n, hmax⟩ := exists_tiltedBinomialMass_maximizer p n
    obtain ⟨hkLower, hnkLower⟩ :=
      maximizer_is_in_quarter_window hpHalf hpTwoThird hnLarge hk₀n hmax
    have hk₀ : 0 < k₀ := by
      have hnR : 0 < (n : ℝ) := by positivity
      have : 0 < (k₀ : ℝ) :=
        lt_of_lt_of_le (by positivity : 0 < (n : ℝ) / 4) hkLower
      exact_mod_cast this
    have hk₀n' : k₀ < n := by
      have hdiff : 0 < n - k₀ := by
        have hnR : 0 < (n : ℝ) := by positivity
        have : 0 < ((n - k₀ : ℕ) : ℝ) :=
          lt_of_lt_of_le (by positivity : 0 < (n : ℝ) / 4) hnkLower
        exact_mod_cast this
      omega
    have hkmax : tiltedBinomialMass p n k ≤ tiltedBinomialMass p n k₀ := by
      by_cases hkn : k ≤ n
      · exact hmax k hkn
      · have hnk : n < k := Nat.lt_of_not_ge hkn
        have hzero : tiltedBinomialMass p n k = 0 := by
          simp [tiltedBinomialMass, Nat.choose_eq_zero_of_lt hnk]
        rw [hzero]
        exact tiltedBinomialMass_nonneg hp₀.le hp₁.le n k₀
    calc
      tiltedBinomialMass p n k ≤ tiltedBinomialMass p n k₀ := hkmax
      _ ≤ C₀ / Real.sqrt n :=
        hcentral n k₀ hn hk₀ hk₀n' hkLower hnkLower
      _ ≤ max C₀ 3 / Real.sqrt n := by
        exact div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  · have hnNine : n ≤ 9 := by omega
    have hmass := tiltedBinomialMass_le_one hp₀.le hp₁.le n k
    have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hsqrt : Real.sqrt (n : ℝ) ≤ 3 := by
      calc
        Real.sqrt (n : ℝ) ≤ Real.sqrt 9 :=
          Real.sqrt_le_sqrt (by exact_mod_cast hnNine)
        _ = 3 := by
          rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num,
            Real.sqrt_sq_eq_abs]
          norm_num
    have hone : (1 : ℝ) ≤ 3 / Real.sqrt n := by
      rw [le_div_iff₀ hsqrtPos]
      simpa using hsqrt
    exact hmass.trans (hone.trans (div_le_div_of_nonneg_right
      (le_max_right C₀ 3) (Real.sqrt_nonneg _)))
end FirstPassageLinearTransport
