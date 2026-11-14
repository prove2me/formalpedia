-- Prove2me | solution 1 for ConsistentSubmodular.sampleExpectation_card_upper_tail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:25.07112+00:00
-- url     : https://prove2.me/submissions/1059c4bd-7983-4a0c-87c2-c320c1e509b8

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

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem solution (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {κ b : ℝ} (hmass : ∑ i ∈ U, p i ≤ κ)
    (hb : 0 < b) (hb2 : b ≤ 2 * κ) :
    sampleExpectation U p (fun S => if κ + b < (S.card : ℝ) then 1 else 0) ≤
      Real.exp (-(b ^ 2) / (4 * κ)) := by
  have hκ : 0 < κ := by linarith
  set s := b / (2 * κ) with hsdef
  have hs0 : 0 ≤ s := div_nonneg hb.le (by linarith)
  have hs1 : s ≤ 1 := (div_le_one (by linarith)).mpr hb2
  have hpoint : ∀ S ⊆ U, (if κ + b < (S.card : ℝ) then (1 : ℝ) else 0) ≤
      Real.exp (-s * (κ + b)) * Real.exp (s * S.card) := by
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
  have hquad : Real.exp s - 1 ≤ s + s ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := s) (by rw [abs_of_nonneg hs0]; exact hs1)
    linarith [le_abs_self (Real.exp s - 1 - s)]
  have hm := mul_le_mul_of_nonneg_left hmass hes
  have hκs : (Real.exp s - 1) * κ ≤ (s + s ^ 2) * κ := mul_le_mul_of_nonneg_right hquad hκ.le
  have hfinal : -s * (κ + b) + (s + s ^ 2) * κ = -(b ^ 2) / (4 * κ) := by
    rw [hsdef]
    field_simp
    ring
  linarith

end
