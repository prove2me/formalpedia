-- Prove2me | solution 1 for BidPriceControl.Asymptotic.scaled_optimum_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:01:41.289195+00:00
-- url     : https://prove2.me/submissions/6ea16365-53de-499e-8be6-6a6e7765a682

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model
import Theorems.Thm_BidPriceControl_Asymptotic_lemma1_upper_bound
import Theorems.Thm_BidPriceControl_Asymptotic_relaxed_value_scaling

open MeasureTheory ProbabilityTheory

open BidPriceControl.Asymptotic in
theorem solution {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (μstar : Fin m → ℝ) (hmin : IsRelaxedMinimizer A F k x μstar) (θ : ℕ) (hθ : 1 ≤ θ) :
    optValue A (scaledLaw F θ) (θ * k) (θ • x) ≤ (θ : ℝ) * relaxedValue A F k x μstar := by
  have hFs : ∀ t ∈ Finset.Icc 1 (θ * k), IsRequestLaw (scaledLaw F θ t) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    apply hF
    rw [Finset.mem_Icc]
    have hθ0 : 0 < θ := hθ
    constructor
    · rw [Nat.le_div_iff_mul_le hθ0]; omega
    · rw [Nat.div_le_iff_le_mul_add_pred hθ0]
      have : t ≤ k * θ := by rw [mul_comm]; exact ht.2
      omega
  rw [← (relaxed_value_scaling A F k x θ hθ).1 μstar]
  exact lemma1_upper_bound A (scaledLaw F θ) (θ * k) (θ • x) hFs μstar hmin.1
