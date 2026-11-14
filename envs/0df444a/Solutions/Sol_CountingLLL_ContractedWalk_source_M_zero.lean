-- Prove2me | solution 1 for CountingLLL.ContractedWalk.source_M_zero
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:10:59.883639+00:00
-- url     : https://prove2.me/submissions/c969fd53-54c8-4c88-b4ed-c873b281dbb1

import Definitions.Def_CountingLLL_ContractedCost
set_option autoImplicit false
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal BigOperators

/-- The paper's weighted-change quantity M in the zero-upward-probability case. -/
theorem solution : expectedWeightedChanges 0 3 2 = (3:ℝ≥0∞)/2 := by
  let ω0 : Tape := fun _ => false
  have hbit : bitLaw 0 = Measure.dirac false := by simp [bitLaw]
  have hlaw : tapeLaw 0 = Measure.dirac ω0 := by
    simp [tapeLaw, hbit, ω0]
  have hz (m : ℕ) : level ω0 3 (3+m) = 0 := by
    induction m with
    | zero => rfl
    | succ m ih => simpa [Nat.add_succ, level, ih]
  have hu (t : ℕ) : upwardBefore ω0 3 t = 0 := by simp [upwardBefore, ω0]
  have hw : weightedChanges ω0 3 2 = (3:ℝ≥0∞)/2 := by
    unfold weightedChanges
    rw [tsum_eq_sum (s := Finset.range 3)]
    · norm_num [Finset.sum_range_succ, changeWeight, level, hu, ω0]
      rw [div_eq_mul_inv]
      ring
    · intro t ht
      have ht' : 3 ≤ t := by simpa using ht
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ht'
      simp [changeWeight, hz]
  unfold expectedWeightedChanges
  rw [hlaw, lintegral_dirac]
  exact hw
