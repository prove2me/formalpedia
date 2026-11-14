-- Prove2me | solution 1 for ConsistentSubmodular.Objective.sampleAdd_mono_probability
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:27:47.584389+00:00
-- url     : https://prove2.me/submissions/c90709f3-b3d8-4fcf-82dd-19e6447054fb

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalSampling
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_insert

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem sampleAdd_insert (U : Finset ι) {e : ι} (he : e ∉ U)
    (p : ι → ℝ) (v : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd (insert e U) p v B =
      (1 - p e) * sampleAdd U p v B + p e * sampleAdd U p v (insert e B) := by
  unfold sampleAdd
  rw [sampleExpectation_insert U he]
  simp only [Finset.union_insert, Finset.insert_union]

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution (U : Finset (Fin n)) (p q : Fin n → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ U, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ U, p i ≤ q i) (B : Finset (Fin n)) :
    sampleAdd U p f.value B ≤ sampleAdd U q f.value B := by
  induction U using Finset.induction_on generalizing B with
  | empty => simp
  | @insert e U he ih =>
    have hpU : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1 := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have hqU : ∀ i ∈ U, 0 ≤ q i ∧ q i ≤ 1 := fun i hi => hq i (Finset.mem_insert_of_mem hi)
    have hpqU : ∀ i ∈ U, p i ≤ q i := fun i hi => hpq i (Finset.mem_insert_of_mem hi)
    rw [sampleAdd_insert U he, sampleAdd_insert U he]
    have h0 := mul_le_mul_of_nonneg_left (ih hpU hqU hpqU B)
      (sub_nonneg.mpr (hp e (Finset.mem_insert_self e U)).2)
    have h1 := mul_le_mul_of_nonneg_left (ih hpU hqU hpqU (insert e B))
      (hp e (Finset.mem_insert_self e U)).1
    have hm := (f.sampled U q hqU).monotone B (insert e B) (Finset.subset_insert e B)
    have hdiff := mul_nonneg (sub_nonneg.mpr (hpq e (Finset.mem_insert_self e U))) (sub_nonneg.mpr hm)
    change 0 ≤ (q e - p e) * (sampleAdd U q f.value (insert e B) - sampleAdd U q f.value B) at hdiff
    nlinarith only [h0, h1, hdiff]

end
