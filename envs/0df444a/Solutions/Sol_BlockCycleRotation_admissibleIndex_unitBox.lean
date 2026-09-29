-- Prove2me | solution 1 for BlockCycleRotation.admissibleIndex_unitBox
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:02:41.678089+00:00
-- url     : https://prove2.me/submissions/318ef4d0-9531-404d-a771-cc330740424a

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

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
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- The boxes of the uniform subdivision of `[0,1]` are indexed by `0,…,n-1`. -/
theorem solution (n : ℕ) [NeZero n] :
    unitPartition.admissibleIndex n unitBox
      = (Finset.range n).image (fun j : ℕ => (fun _ : Fin 1 => (j : ℤ))):= by
  have hn : 0 < n := Nat.pos_of_neZero n
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  ext ν
  rw [unitPartition.mem_admissibleIndex_iff, Box.le_iff_bounds, Finset.mem_image]
  simp only [unitPartition.box_lower, unitPartition.box_upper, unitBox, Pi.le_def]
  constructor
  · rintro ⟨hl, hu⟩
    have h1 : (0 : ℝ) ≤ (ν 0 : ℝ) / (n : ℝ) := hl 0
    have h2 : ((ν 0 : ℝ) + 1) / (n : ℝ) ≤ 1 := hu 0
    rw [le_div_iff₀ hnR, zero_mul] at h1
    rw [div_le_one hnR] at h2
    have h1' : (0 : ℤ) ≤ ν 0 := by exact_mod_cast h1
    have h2' : ν 0 + 1 ≤ (n : ℤ) := by exact_mod_cast h2
    refine ⟨(ν 0).toNat, Finset.mem_range.2 (by omega), ?_⟩
    funext i
    have : i = 0 := Subsingleton.elim _ _
    rw [this]
    omega
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_range] at hj
    have hjR : (j : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hj
    constructor
    · intro i; positivity
    · intro i
      rw [div_le_one hnR]
      push_cast
      linarith
