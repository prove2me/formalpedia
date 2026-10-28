-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_signed_powers_exist_dominated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T16:50:09.799623+00:00
-- url     : https://prove2.me/submissions/d293333a-16ee-4c13-b7d0-903be8d1c525

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_power_sequence_exists
import Theorems.Thm_AvramDividend_Classical_causal_l1_measurable_signed_products
import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real
import Theorems.Thm_AvramDividend_Classical_causal_signed_powers_domination_induction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

/-- Signed L1 powers exist and inherit a positive causal envelope pointwise. -/
theorem solution
    (k κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hkmeas : Measurable k)
    (hkdom : ∀ t : ℝ, 0 ≤ t → |k t| ≤ κ t)
    (hF0 : F 0 = κ)
    (hFrec : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        κ s * F n (x - s) ∂volume)
    (hFint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => κ (x - s) * F n s) volume 0 x) :
    ∃ P : ℕ → ℝ → ℝ,
      P 0 = k ∧
      (∀ n : ℕ, P (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
          k s * P n (x - s) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → |P n t| ≤ F n t) := by
  rcases causal_l1_convolution_power_sequence_exists k hkL1 with
    ⟨P, hP0, hPrec, hPL1, _⟩
  have hPint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      P (n + 1) x = ∫ s in (0 : ℝ)..x, k (x - s) * P n s := by
    intro n x hx
    calc
      P (n + 1) x =
          ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume := by
            rw [hPrec n]
      _ = ∫ s in Ioc (0 : ℝ) x, P n s * k (x - s) ∂volume :=
        positive_Ioc_causal_convolution_comm_real k (P n) x (le_of_lt hx)
      _ = ∫ s in (0 : ℝ)..x, k (x - s) * P n s := by
        rw [intervalIntegral.integral_of_le (le_of_lt hx)]
        congr 1
        funext s
        ring
  have hFintRec : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F (n + 1) x = ∫ s in (0 : ℝ)..x, κ (x - s) * F n s := by
    intro n x hx
    calc
      F (n + 1) x =
          ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume := by
            rw [hFrec n]
      _ = ∫ s in Ioc (0 : ℝ) x, F n s * κ (x - s) ∂volume :=
        positive_Ioc_causal_convolution_comm_real κ (F n) x (le_of_lt hx)
      _ = ∫ s in (0 : ℝ)..x, κ (x - s) * F n s := by
        rw [intervalIntegral.integral_of_le (le_of_lt hx)]
        congr 1
        funext s
        ring
  have hPzero : ∀ n : ℕ, |P n 0| ≤ F n 0 := by
    intro n
    cases n with
    | zero => simpa [hP0, hF0] using hkdom 0 (le_refl 0)
    | succ n =>
        have hp : P (n + 1) 0 = 0 := by rw [hPrec n]; simp
        have hf : F (n + 1) 0 = 0 := by rw [hFrec n]; simp
        simp [hp, hf]
  have hMeas := causal_l1_measurable_signed_products k P hkmeas hPL1
  have hDom := causal_signed_powers_domination_induction k κ P F
    hkdom hP0 hF0 hPint hFintRec hPzero hMeas hFint
  exact ⟨P, hP0, hPrec, hPL1, hDom⟩
