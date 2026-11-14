-- Prove2me | solution 1 for ConsistentSubmodular.sampleExpectation_exp_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:30:20.485258+00:00
-- url     : https://prove2.me/submissions/426cb3e8-93e1-4be6-b7f6-b938d7d48a49

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_insert

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

theorem sampleExpectation_congr (U : Finset ι) (p : ι → ℝ) {v w : Finset ι → ℝ}
    (h : ∀ S ⊆ U, v S = w S) : sampleExpectation U p v = sampleExpectation U p w := by
  exact Finset.sum_congr rfl (fun S hS => by rw [h S (Finset.mem_powerset.mp hS)])

theorem sampleExpectation_nonnegative (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {v : Finset ι → ℝ}
    (hv : ∀ S ⊆ U, 0 ≤ v S) : 0 ≤ sampleExpectation U p v := by
  exact Finset.sum_nonneg (fun S hS => mul_nonneg
    (subsetWeight_nonnegative U p hp (Finset.mem_powerset.mp hS)) (hv S (Finset.mem_powerset.mp hS)))

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem solution (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    sampleExpectation U p (fun S => Real.exp (s * S.card)) ≤
      Real.exp ((Real.exp s - 1) * ∑ i ∈ U, p i) := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert u U hu ih =>
    have hpU : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1 := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    obtain ⟨hpu0, hpu1⟩ := hp u (Finset.mem_insert_self u U)
    rw [sampleExpectation_insert U hu]
    have hcongr : sampleExpectation U p (fun S => Real.exp (s * ((insert u S).card : ℝ))) =
        Real.exp s * sampleExpectation U p (fun S => Real.exp (s * S.card)) := by
      rw [← sampleExpectation_mul]
      apply sampleExpectation_congr
      intro S hS
      have huS : u ∉ S := fun h => hu (hS h)
      rw [Finset.card_insert_of_notMem huS]
      push_cast
      rw [mul_add, mul_one, Real.exp_add]
      ring
    rw [hcongr, Finset.sum_insert hu]
    have hE0 : 0 ≤ sampleExpectation U p (fun S => Real.exp (s * S.card)) :=
      sampleExpectation_nonnegative U p hpU (fun S _ => (Real.exp_pos _).le)
    have hes : 0 ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s]
    calc (1 - p u) * sampleExpectation U p (fun S => Real.exp (s * S.card)) +
          p u * (Real.exp s * sampleExpectation U p (fun S => Real.exp (s * S.card)))
        = (1 + p u * (Real.exp s - 1)) *
            sampleExpectation U p (fun S => Real.exp (s * S.card)) := by ring
      _ ≤ Real.exp (p u * (Real.exp s - 1)) *
            Real.exp ((Real.exp s - 1) * ∑ i ∈ U, p i) :=
          mul_le_mul (by linarith [Real.add_one_le_exp (p u * (Real.exp s - 1))]) (ih hpU) hE0
            (Real.exp_pos _).le
      _ = Real.exp ((Real.exp s - 1) * (p u + ∑ i ∈ U, p i)) := by
          rw [← Real.exp_add]; ring_nf

end
