-- Prove2me | solution 1 for BookProof.QuantizationWeyl.exp_Ngen
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:24.853095+00:00
-- url     : https://prove2.me/submissions/4c088477-5b09-4e96-bf47-e5913f22c3eb

-- Generated from ChapterQuantizationWeyl.lean — solution of BookProof.QuantizationWeyl.exp_Ngen
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
import Theorems.Thm_BookProof_QuantizationWeyl_Ngen_cube
import Theorems.Thm_BookProof_QuantizationWeyl_Ngen_sq
open BookProof.QuantizationWeyl



open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option maxHeartbeats 1000000 in
theorem solution (a b c : ℝ) :
    NormedSpace.exp (Ngen a b c) = Heis a b (c + a * b / 2) := by

  have hcube := Ngen_cube a b c
  have h := congrFun (NormedSpace.exp_eq_tsum ℝ (𝔸 := M)) (Ngen a b c)
  rw [h, tsum_eq_sum (s := Finset.range 3) ?_]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, Ngen_sq]
    unfold Ngen Zgen Heis
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, pow_succ] ; ring
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    have : (Ngen a b c) ^ k = 0 := by
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [pow_add, hcube, zero_mul]
    rw [this, smul_zero]
