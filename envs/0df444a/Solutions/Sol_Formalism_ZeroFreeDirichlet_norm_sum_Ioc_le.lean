-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.norm_sum_Ioc_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:45:12.780653+00:00
-- url     : https://prove2.me/submissions/8157fb55-8d46-42d4-95cb-84b79487a89a

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SumVonMangoldtNotCoprimeLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ Λ n) {y Y : ℝ} (hy : 1 ≤ y) (hyY : y ≤ Y) :
    ‖∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖
      ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by
  have hY1 : 1 ≤ Y := le_trans hy hyY
  have hterm : ∀ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊,
      ‖f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖ ≤ (Y - y) * Real.log Y := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : y < (n : ℝ) := by
      have := Nat.lt_floor_add_one y
      have h2 : ((⌊y⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
      linarith
    have hn2 : (n : ℝ) ≤ Y := by
      have := Nat.floor_le (show 0 ≤ Y by linarith)
      have h2 : (n : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast hn.2
      linarith
    have hnpos : (0:ℝ) < n := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hA : 0 ≤ y * (Y / n - 1) := by
      apply mul_nonneg (by linarith)
      rw [sub_nonneg, le_div_iff₀ hnpos]; linarith
    have hB : y * (Y / n - 1) ≤ Y - y := by
      have e : y * (Y / n - 1) = (Y - n) * (y / n) := by field_simp
      rw [e]
      have h3 : y / n ≤ 1 := by rw [div_le_one hnpos]; linarith
      have h4 : 0 ≤ Y - n := by linarith
      nlinarith
    rw [abs_of_nonneg hA]
    have hf' : ‖f n‖ ≤ Real.log Y :=
      calc ‖f n‖ ≤ Λ n := hf n
        _ ≤ Real.log n := vonMangoldt_le_log
        _ ≤ Real.log Y := Real.log_le_log hnpos hn2
    calc ‖f n‖ * (y * (Y / n - 1)) ≤ Real.log Y * (Y - y) :=
          mul_le_mul hf' hB hA (Real.log_nonneg hY1)
      _ = (Y - y) * Real.log Y := by ring
  calc _ ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, ‖f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, (Y - y) * Real.log Y := Finset.sum_le_sum hterm
    _ = ((Ioc ⌊y⌋₊ ⌊Y⌋₊).card : ℝ) * ((Y - y) * Real.log Y) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by linarith) (Real.log_nonneg hY1))
      rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono hyY)]
      have h1 := Nat.floor_le (show 0 ≤ Y by linarith)
      have h2 := Nat.lt_floor_add_one y
      linarith
end Formalism.ZeroFreeDirichlet
