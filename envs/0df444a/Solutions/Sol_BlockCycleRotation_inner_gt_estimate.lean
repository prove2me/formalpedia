-- Prove2me | solution 1 for BlockCycleRotation.inner_gt_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:19:46.573107+00:00
-- url     : https://prove2.me/submissions/65060660-aaa1-4c8e-a580-e7e27fc45de9

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_sum_ap_sub_main_le_log_real
import Theorems.Thm_BlockCycleRotation_inner_gt_sum_eq
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **The innermost estimation layer.**  For a fixed pair `(a, a')`, the inner
sum differs from its expected value by `O(log a)` times the size of the
coefficients — the paper's `G₂ + G₃` for that pair. -/
theorem solution {m d a a' : ℕ} (ha : 0 < a) (hgcd : Nat.gcd a a' = 1) (U : ℕ)
    (hU : ∀ b' ∈ Finset.Ico 1 U, a' * b' ≤ m) :
    ∃ c : ℤ,
      |((∑ b' ∈ (Finset.Ico 1 U).filter (fun b' => a ∣ (m - a' * b')),
            (d * a + (m - a' * b') / a) : ℕ) : ℝ)
          - (1 / (a : ℝ)) * ∑ b' ∈ Finset.Ico 1 U,
              ((((d * a : ℕ) : ℝ) + (m : ℝ) / a) + (-(a' : ℝ) / a) * b')|
        ≤ (|((d * a : ℕ) : ℝ) + (m : ℝ) / a| + |(-(a' : ℝ) / a)| * (U - 1 : ℕ))
            * (1 + Real.log a):= by
  obtain ⟨c, hc⟩ := inner_gt_sum_eq (m := m) (d := d) ha hgcd
  refine ⟨c, ?_⟩
  rw [hc U hU]
  exact sum_ap_sub_main_le_log_real ha c _ _ U
