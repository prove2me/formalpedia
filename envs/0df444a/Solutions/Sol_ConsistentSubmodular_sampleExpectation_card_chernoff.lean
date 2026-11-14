-- Prove2me | solution 1 for ConsistentSubmodular.sampleExpectation_card_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:25.90648+00:00
-- url     : https://prove2.me/submissions/44f0e00b-4e94-486c-a67d-4e10bbaddeb2

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_exp_card_le

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem sampleExpectation_mul (U : Finset ι) (p : ι → ℝ) (c : ℝ) (v : Finset ι → ℝ) :
    sampleExpectation U p (fun S => c * v S) = c * sampleExpectation U p v := by
  simp only [sampleExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

/-- `exp s ≤ 1 + s + s²/2 + 2 s³/9` for `0 ≤ s ≤ 1`. -/
theorem exp_le_cubic {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp s ≤ 1 + s + s ^ 2 / 2 + 2 / 9 * s ^ 3 := by
  have h := Real.exp_bound' hs0 hs1 (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
    Nat.cast_ofNat, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMul, pow_zero, pow_one,
    zero_add, div_one] at h
  linarith

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem solution (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {κ η : ℝ} (hmass : ∑ i ∈ U, p i ≤ κ)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    sampleExpectation U p (fun S => if (1 + η) * κ < (S.card : ℝ) then 1 else 0) ≤
      Real.exp (-(η ^ 2) * κ / 3) := by
  have hκ : 0 ≤ κ := (Finset.sum_nonneg fun i hi => (hp i hi).1).trans hmass
  set s := η - η ^ 2 / 3 with hsdef
  have hs0 : 0 ≤ s := by nlinarith
  have hs1 : s ≤ 1 := by nlinarith
  have hpoint : ∀ S ⊆ U, (if (1 + η) * κ < (S.card : ℝ) then (1 : ℝ) else 0) ≤
      Real.exp (-s * ((1 + η) * κ)) * Real.exp (s * S.card) := by
    intro S _
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp_iff.mpr
      nlinarith
    · exact (Real.exp_pos _).le
  have hP := sampleExpectation_mono U p hp hpoint
  rw [sampleExpectation_mul] at hP
  have hmgf := sampleExpectation_exp_card_le U p hp hs0
  have hbound := hP.trans (mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le)
  rw [← Real.exp_add] at hbound
  refine hbound.trans (Real.exp_le_exp.mpr ?_)
  have hes : 0 ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s]
  have hm := mul_le_mul_of_nonneg_left hmass hes
  have hcubic := exp_le_cubic hs0 hs1
  -- `e^s - 1 - s (1 + η) ≤ -η²/3` at `s = η - η²/3`, for `0 < η ≤ 1`.
  have hkey : Real.exp s - 1 - s * (1 + η) ≤ -(η ^ 2) / 3 := by
    have hpoly : s + s ^ 2 / 2 + 2 / 9 * s ^ 3 - s * (1 + η) ≤ -(η ^ 2) / 3 := by
      rw [hsdef]
      nlinarith [sq_nonneg (η - 2 / 3), pow_le_one₀ hη.le hη1 (n := 3), pow_nonneg hη.le 4,
        mul_nonneg (sq_nonneg η) (sq_nonneg (η - 2 / 3)), mul_nonneg (pow_nonneg hη.le 3)
          (sub_nonneg.mpr hη1), sq_nonneg η]
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hkey hκ]

end
