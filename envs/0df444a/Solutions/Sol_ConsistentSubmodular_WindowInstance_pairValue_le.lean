-- Prove2me | solution 1 for ConsistentSubmodular.WindowInstance.pairValue_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:29.472721+00:00
-- url     : https://prove2.me/submissions/f4a4f1ca-4939-4ece-bdea-ae9d891a3d65

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_WindowBounds
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_insert
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_inter_zero

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

theorem finiteExpectation_eq_sampleExpectation [Fintype ι] (p : ι → ℝ) (U : Finset ι)
    (hp : ∀ i ∉ U, p i = 0) (v : Finset ι → ℝ) :
    finiteExpectation p v = sampleExpectation U p v := by
  rw [← sampleExpectation_univ, sampleExpectation_inter_zero U Finset.univ p hp,
    Finset.univ_inter]

theorem sampleExpectation_singleton (p : ι → ℝ) (a : ι) (v : Finset ι → ℝ) :
    sampleExpectation {a} p v = (1 - p a) * v ∅ + p a * v {a} := by
  have h := sampleExpectation_insert (∅ : Finset ι) (Finset.notMem_empty a) p v
  simpa using h

theorem sampleExpectation_pair (p : ι → ℝ) {a b : ι} (hab : a ≠ b) (v : Finset ι → ℝ) :
    sampleExpectation {a, b} p v =
      (1 - p a) * ((1 - p b) * v ∅ + p b * v {b}) +
        p a * ((1 - p b) * v {a} + p b * v {a, b}) := by
  rw [sampleExpectation_insert {b} (by simpa using hab) p v, sampleExpectation_singleton,
    sampleExpectation_singleton]
  rfl

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

theorem mixtureValue_vertex (j i : Fin (W.lastStage + 1)) :
    W.mixtureValue j (vertex i) = W.objective.value (W.arrivals j ∪ W.candidate i) := by
  change finiteExpectation (vertex i)
    (fun I => W.objective.value (W.arrivals j ∪ I.biUnion W.candidate)) = _
  rw [finiteExpectation_eq_sampleExpectation _ {i} (fun k hk => by
      simp only [Finset.mem_singleton] at hk
      simp [vertex, hk]),
    sampleExpectation_singleton]
  simp [vertex]

end WindowInstance

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
open ConsistentSubmodular.WindowInstance
variable {n : ℕ} (W : WindowInstance n)

theorem solution (j a b : Fin (W.lastStage + 1)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    W.pairValue j a b s ≤ W.mixtureValue j (mix (vertex a) (vertex b) s) := by
  by_cases hab : a = b
  · subst b
    rw [mix_self, mixtureValue_vertex]
    have hm := W.objective.monotone (W.arrivals j) (W.arrivals j ∪ W.candidate a)
      Finset.subset_union_left
    have hq : 0 ≤ s * (1 - s) := mul_nonneg hs0 (by linarith)
    unfold pairValue twoTypeValue
    rw [Finset.union_self]
    nlinarith
  · have hpa : mix (vertex a) (vertex b) s a = 1 - s := by
      simp [mix, vertex, hab]
    have hpb : mix (vertex a) (vertex b) s b = s := by
      simp [mix, vertex, Ne.symm hab]
    change _ ≤ finiteExpectation (mix (vertex a) (vertex b) s)
      (fun I => W.objective.value (W.arrivals j ∪ I.biUnion W.candidate))
    rw [finiteExpectation_eq_sampleExpectation _ {a, b} (fun k hk => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        simp [mix, vertex, hk.1, hk.2]),
      sampleExpectation_pair _ hab, hpa, hpb]
    have hU : ({a, b} : Finset (Fin (W.lastStage + 1))).biUnion W.candidate =
        W.candidate a ∪ W.candidate b := by
      rw [Finset.biUnion_insert, Finset.singleton_biUnion]
    simp only [Finset.biUnion_empty, Finset.union_empty, Finset.singleton_biUnion, hU]
    unfold pairValue twoTypeValue
    apply le_of_eq
    ring

end
