-- Prove2me | solution 1 for ConsistentSubmodular.physical_multilinear_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:58.58021+00:00
-- url     : https://prove2.me/submissions/495e73a8-11f3-4773-b604-f4a5525a6e2d

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalSampling
import Theorems.Thm_ConsistentSubmodular_Objective_sampleAdd_mono_probability
import Theorems.Thm_ConsistentSubmodular_unionProbability_mem_unitInterval
import Theorems.Thm_ConsistentSubmodular_type_expectation_le_independent_union

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n m : ℕ}

theorem physicalProbability_nonnegative
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i) (e : Fin n) : 0 ≤ physicalProbability cores p e := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hp i
  · rfl

theorem physicalProbability_le_mass
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i) (e : Fin n) :
    physicalProbability cores p e ≤ ∑ i, p i := by
  exact Finset.sum_le_sum (fun i _ => by split_ifs <;> simp_all)

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem sampleExpectation_univ [Fintype ι] (p : ι → ℝ) (v : Finset ι → ℝ) :
    sampleExpectation Finset.univ p v = finiteExpectation p v := by
  simp [sampleExpectation, finiteExpectation, subsetWeight, bernoulliWeight,
    Finset.compl_eq_univ_sdiff]

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

variable {n : ℕ}

theorem unionProbability_insert (cores : ι → Finset (Fin n)) (U : Finset ι)
    {i : ι} (hi : i ∉ U) (p : ι → ℝ) (e : Fin n) :
    unionProbability cores (insert i U) p e = unionProbability cores U p e +
      (if e ∈ cores i then p i else 0) - unionProbability cores U p e * (if e ∈ cores i then p i else 0) := by
  unfold unionProbability
  rw [Finset.prod_insert hi]
  split_ifs <;> ring

theorem unionProbability_le_sum (cores : ι → Finset (Fin n)) (U : Finset ι)
    (p : ι → ℝ) (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (e : Fin n) :
    unionProbability cores U p e ≤ ∑ i ∈ U, if e ∈ cores i then p i else 0 := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert i U hi ih =>
    have hpU : ∀ j ∈ U, 0 ≤ p j ∧ p j ≤ 1 := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    rw [unionProbability_insert cores U hi, Finset.sum_insert hi]
    have hbase := (unionProbability_mem_unitInterval cores U p hpU e).1
    have hpi : 0 ≤ (if e ∈ cores i then p i else 0) := by
      split_ifs
      · exact (hp i (Finset.mem_insert_self i U)).1
      · rfl
    have hmul := mul_nonneg hbase hpi
    have hrec := ih hpU
    linarith

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
variable {n : ℕ}

theorem solution {m : ℕ} (f : Objective n)
    (cores : Fin (m + 1) → Finset (Fin n)) (B : Finset (Fin n)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i) (hmass : (∑ i, p i) ≤ 1) :
    finiteExpectation p (f.onTypes cores B).value ≤
      finiteExpectation (physicalProbability cores p) (fun S => f.value (B ∪ S)) := by
  have hpcube : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := by
    intro i
    exact ⟨hp i, (Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)).trans hmass⟩
  have hqcube : ∀ e ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ unionProbability cores Finset.univ p e ∧ unionProbability cores Finset.univ p e ≤ 1 :=
    fun e _ => unionProbability_mem_unitInterval cores Finset.univ p (fun i _ => hpcube i) e
  have hzcube : ∀ e ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ physicalProbability cores p e ∧ physicalProbability cores p e ≤ 1 := by
    intro e _
    exact ⟨physicalProbability_nonnegative cores p hp e, (physicalProbability_le_mass cores p hp e).trans hmass⟩
  have htype := type_expectation_le_independent_union f cores Finset.univ p (fun i _ => hpcube i) B
  have hmono := f.sampleAdd_mono_probability Finset.univ (unionProbability cores Finset.univ p)
    (physicalProbability cores p) hqcube hzcube
    (fun e _ => unionProbability_le_sum cores Finset.univ p (fun i _ => hpcube i) e) B
  have h := htype.trans hmono
  simpa only [sampleAdd, sampleExpectation_univ, Objective.onTypes] using h

end
