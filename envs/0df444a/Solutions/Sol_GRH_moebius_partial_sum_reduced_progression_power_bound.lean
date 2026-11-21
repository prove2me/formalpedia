-- Prove2me | solution 1 for GRH.moebius_partial_sum_reduced_progression_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:26:24.986835+00:00
-- url     : https://prove2.me/submissions/0cb12b65-1e72-4415-bf22-02497160d15a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_moebius_progression_le_of_liouville_progression_le
import Theorems.Thm_GRH_liouville_partial_sum_reduced_progression_power_bound
import Mathlib
open GRH
theorem solution
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |∑ k ∈ Finset.range (n + 1),
        if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0| ≤
          C * ((n : ℝ) + 1) ^ σ := by
  obtain ⟨C,hC,hL⟩ := liouville_partial_sum_reduced_progression_power_bound q σ hhalf hone
  refine ⟨C * (2:ℝ)^σ * ∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹,?_,?_⟩
  · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))
      (tsum_nonneg fun d => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg d) _))
  · intro n
    exact moebius_progression_le_of_liouville_progression_le q σ C hhalf hC hL a ha n
