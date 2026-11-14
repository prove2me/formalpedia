-- Prove2me | solution 1 for ConsistentSubmodular.sampleExpectation_exp_neg_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:32.661915+00:00
-- url     : https://prove2.me/submissions/5028d6f8-ae08-4b1d-b3b5-d3fc75646b63

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_insert
import Theorems.Thm_ConsistentSubmodular_exp_moment_step

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem sampleExpectation_nonnegative (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {v : Finset ι → ℝ}
    (hv : ∀ S ⊆ U, 0 ≤ v S) : 0 ≤ sampleExpectation U p v := by
  exact Finset.sum_nonneg (fun S hS => mul_nonneg
    (subsetWeight_nonnegative U p hp (Finset.mem_powerset.mp hS)) (hv S (Finset.mem_powerset.mp hS)))

theorem sampleExpectation_sub (U : Finset ι) (p : ι → ℝ) (v w : Finset ι → ℝ) :
    sampleExpectation U p (fun S => v S - w S) = sampleExpectation U p v - sampleExpectation U p w := by
  simp only [sampleExpectation, mul_sub, Finset.sum_sub_distrib]

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem sampleExpectation_le_const (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {v : Finset ι → ℝ} {c : ℝ}
    (hv : ∀ S ⊆ U, v S ≤ c) : sampleExpectation U p v ≤ c := by
  have h := sampleExpectation_mono U p hp (v := v) (w := fun _ => c) hv
  rwa [sampleExpectation_const] at h

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem solution (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (G : Finset ι → ℝ)
    (hmono : ∀ A B, A ⊆ B → G A ≤ G B)
    (hsub : ∀ A B, G (A ∪ B) + G (A ∩ B) ≤ G A + G B)
    (hcap : ∀ A e, G (insert e A) - G A ≤ 1) (lam : ℝ) :
    sampleExpectation U p (fun S => Real.exp (-lam * G S)) ≤
      Real.exp (-lam * G ∅ + (sampleExpectation U p G - G ∅) * (Real.exp (-lam) - 1)) := by
  induction U using Finset.induction_on generalizing G with
  | empty => simp
  | @insert u U hu ih =>
    have hpU : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1 := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    obtain ⟨hpu0, hpu1⟩ := hp u (Finset.mem_insert_self u U)
    let G1 : Finset ι → ℝ := fun S => G (insert u S)
    have h1mono : ∀ A B, A ⊆ B → G1 A ≤ G1 B :=
      fun A B h => hmono _ _ (Finset.insert_subset_insert u h)
    have h1sub : ∀ A B, G1 (A ∪ B) + G1 (A ∩ B) ≤ G1 A + G1 B := by
      intro A B
      have h := hsub (insert u A) (insert u B)
      have hu1 : insert u (A ∪ B) = insert u A ∪ insert u B := by
        ext e; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      have hu2 : insert u (A ∩ B) = insert u A ∩ insert u B := by
        ext e; simp only [Finset.mem_insert, Finset.mem_inter]; tauto
      simp only [G1, hu1, hu2]
      exact h
    have h1cap : ∀ A e, G1 (insert e A) - G1 A ≤ 1 := by
      intro A e
      simp only [G1]
      rw [Finset.insert_comm]
      exact hcap _ e
    have h0 := ih hpU G hmono hsub hcap
    have h1 := ih hpU G1 h1mono h1sub h1cap
    have hG1 : G1 ∅ = G {u} := by simp [G1]
    rw [hG1] at h1
    -- The mean marginal of `u` lies between zero and its marginal at the empty set.
    have hδ : sampleExpectation U p G1 - sampleExpectation U p G =
        sampleExpectation U p (fun S => G (insert u S) - G S) := by
      rw [sampleExpectation_sub]
    have hδ0 : 0 ≤ sampleExpectation U p G1 - sampleExpectation U p G := by
      rw [hδ]
      exact sampleExpectation_nonnegative U p hpU (fun S _ =>
        sub_nonneg.mpr (hmono _ _ (Finset.subset_insert u S)))
    have hδd : sampleExpectation U p G1 - sampleExpectation U p G ≤ G {u} - G ∅ := by
      rw [hδ]
      apply sampleExpectation_le_const U p hpU
      intro S hS
      have huS : u ∉ S := fun h => hu (hS h)
      have h := hsub S {u}
      have hi : S ∩ {u} = ∅ := by
        ext e; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty,
          iff_false, not_and]
        rintro he rfl; exact huS he
      have hun : S ∪ {u} = insert u S := by
        ext e; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto
      rw [hi, hun] at h
      linarith
    have hd1 : G {u} - G ∅ ≤ 1 := by simpa using hcap ∅ u
    have hstep := exp_moment_step (lam := lam) hpu0 hδ0 hδd hd1
    rw [sampleExpectation_insert U hu, sampleExpectation_insert U hu]
    change (1 - p u) * sampleExpectation U p (fun S => Real.exp (-lam * G S)) +
        p u * sampleExpectation U p (fun S => Real.exp (-lam * G1 S)) ≤ _
    obtain ⟨a, ha⟩ : ∃ a, a = -lam * G ∅ +
        (sampleExpectation U p G - G ∅) * (Real.exp (-lam) - 1) := ⟨_, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x, x = -lam * (G {u} - G ∅) +
        ((sampleExpectation U p G1 - sampleExpectation U p G) - (G {u} - G ∅)) *
          (Real.exp (-lam) - 1) := ⟨_, rfl⟩
    have h0' : sampleExpectation U p (fun S => Real.exp (-lam * G S)) ≤ Real.exp a := by
      rw [ha]; exact h0
    have h1' : sampleExpectation U p (fun S => Real.exp (-lam * G1 S)) ≤
        Real.exp a * Real.exp x := by
      rw [← Real.exp_add]
      refine h1.trans (le_of_eq ?_)
      congr 1
      rw [ha, hx]
      ring
    rw [← hx] at hstep
    have hpos := Real.exp_pos a
    have hgoal : -lam * G ∅ + ((1 - p u) * sampleExpectation U p G +
        p u * sampleExpectation U p (fun S => G (insert u S)) - G ∅) * (Real.exp (-lam) - 1) =
        a + p u * (sampleExpectation U p G1 - sampleExpectation U p G) *
          (Real.exp (-lam) - 1) := by
      rw [ha]; ring
    rw [hgoal, Real.exp_add]
    calc (1 - p u) * sampleExpectation U p (fun S => Real.exp (-lam * G S)) +
          p u * sampleExpectation U p (fun S => Real.exp (-lam * G1 S))
        ≤ (1 - p u) * Real.exp a + p u * (Real.exp a * Real.exp x) :=
          add_le_add (mul_le_mul_of_nonneg_left h0' (by linarith))
            (mul_le_mul_of_nonneg_left h1' hpu0)
      _ = Real.exp a * ((1 - p u) + p u * Real.exp x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hstep hpos.le

end
