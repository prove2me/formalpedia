-- Prove2me | solution 1 for ConsistentSubmodular.type_expectation_le_independent_union
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:54.761094+00:00
-- url     : https://prove2.me/submissions/34c689b0-8001-48ce-b174-be17f16d3ef8

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalSampling
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_insert
import Theorems.Thm_ConsistentSubmodular_sampleAdd_union_probabilities
import Theorems.Thm_ConsistentSubmodular_Objective_uniform_sample_chord
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_inter_zero
import Theorems.Thm_ConsistentSubmodular_unionProbability_mem_unitInterval

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem sampleAdd_comm (U V : Finset ι) (p q : ι → ℝ) (v : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd U p (sampleAdd V q v) B = sampleAdd V q (sampleAdd U p v) B := by
  unfold sampleAdd sampleExpectation
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.union_right_comm B S T]
  ring

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem sampleExpectation_congr_prob (U : Finset ι) (p q : ι → ℝ)
    (hpq : ∀ i ∈ U, p i = q i) (v : Finset ι → ℝ) :
    sampleExpectation U p v = sampleExpectation U q v := by
  apply Finset.sum_congr rfl
  intro S hS
  have hSU := Finset.mem_powerset.mp hS
  congr 1
  unfold subsetWeight
  congr 1
  · exact Finset.prod_congr rfl (fun i hi => hpq i (hSU hi))
  · exact Finset.prod_congr rfl (fun i hi => by rw [hpq i (Finset.mem_sdiff.mp hi).1])

theorem sampleAdd_mask [Fintype ι] (U : Finset ι) (p : ι → ℝ)
    (v : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd Finset.univ (fun i => if i ∈ U then p i else 0) v B = sampleAdd U p v B := by
  unfold sampleAdd
  rw [sampleExpectation_inter_zero U Finset.univ _ (fun i hi => by simp [hi]), Finset.univ_inter]
  exact sampleExpectation_congr_prob U _ p (fun i hi => by simp [hi]) _

variable {n : ℕ}

theorem unionProbability_insert (cores : ι → Finset (Fin n)) (U : Finset ι)
    {i : ι} (hi : i ∉ U) (p : ι → ℝ) (e : Fin n) :
    unionProbability cores (insert i U) p e = unionProbability cores U p e +
      (if e ∈ cores i then p i else 0) - unionProbability cores U p e * (if e ∈ cores i then p i else 0) := by
  unfold unionProbability
  rw [Finset.prod_insert hi]
  split_ifs <;> ring

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
variable {n : ℕ}

theorem solution (f : Objective n)
    (cores : ι → Finset (Fin n)) (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (B : Finset (Fin n)) :
    sampleExpectation U p (fun I => f.value (B ∪ I.biUnion cores)) ≤
      sampleAdd Finset.univ (unionProbability cores U p) f.value B := by
  induction U using Finset.induction_on generalizing B with
  | empty =>
    simp only [sampleExpectation_empty, Finset.biUnion_empty, Finset.union_empty]
    have hzero : sampleAdd Finset.univ (fun _ : Fin n => 0) f.value B = f.value B := by
      simpa using sampleAdd_mask (∅ : Finset (Fin n)) (fun _ => 0) f.value B
    have hqzero : unionProbability cores ∅ p = fun _ => 0 := funext (unionProbability_empty cores p)
    rw [hqzero]
    exact hzero.ge
  | @insert i U hi ih =>
    have hpU : ∀ j ∈ U, 0 ≤ p j ∧ p j ≤ 1 := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    have hpi := hp i (Finset.mem_insert_self i U)
    have hq : ∀ e ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ unionProbability cores U p e ∧ unionProbability cores U p e ≤ 1 :=
      fun e _ => unionProbability_mem_unitInterval cores U p hpU e
    let g := f.sampled Finset.univ (unionProbability cores U p) hq
    rw [sampleExpectation_insert U hi]
    have hfun : (fun I : Finset ι => f.value (B ∪ (insert i I).biUnion cores)) =
        (fun I : Finset ι => f.value ((B ∪ cores i) ∪ I.biUnion cores)) := by
      funext I
      rw [Finset.biUnion_insert, Finset.union_assoc]
    rw [hfun]
    have h0 := mul_le_mul_of_nonneg_left (ih hpU B) (sub_nonneg.mpr hpi.2)
    have h1 := mul_le_mul_of_nonneg_left (ih hpU (B ∪ cores i)) hpi.1
    have hchord := g.uniform_sample_chord (cores i) B (p i) hpi.1 hpi.2
    change (1 - p i) * sampleAdd Finset.univ (unionProbability cores U p) f.value B +
        p i * sampleAdd Finset.univ (unionProbability cores U p) f.value (B ∪ cores i) ≤
        sampleAdd (cores i) (fun _ => p i) (sampleAdd Finset.univ (unionProbability cores U p) f.value) B at hchord
    have hphysical : sampleAdd (cores i) (fun _ => p i)
        (sampleAdd Finset.univ (unionProbability cores U p) f.value) B =
        sampleAdd Finset.univ (unionProbability cores (insert i U) p) f.value B := by
      rw [sampleAdd_comm]
      have hmask : sampleAdd (cores i) (fun _ => p i) f.value =
          sampleAdd Finset.univ (fun e => if e ∈ cores i then p i else 0) f.value := by
        funext C
        exact (sampleAdd_mask (cores i) (fun _ => p i) f.value C).symm
      rw [hmask, sampleAdd_union_probabilities]
      congr 1
      funext e
      exact (unionProbability_insert cores U hi p e).symm
    rw [hphysical] at hchord
    linarith only [h0, h1, hchord]

end
