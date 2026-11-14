-- Prove2me | solution 1 for ConsistentSubmodular.physical_intersection_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:38.149922+00:00
-- url     : https://prove2.me/submissions/9065b588-94d1-428d-90f3-a50e0497797b

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_CompatibleProfiles
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Simplex
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalMap
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators
import Theorems.Thm_ConsistentSubmodular_physicalProbability_min_le
import Theorems.Thm_ConsistentSubmodular_Objective_sampleAdd_mono_probability
import Theorems.Thm_ConsistentSubmodular_physical_multilinear_lift
import Theorems.Thm_ConsistentSubmodular_Objective_finiteExpectation_min_lower

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n : ℕ}

namespace Objective

variable (f : Objective n)

theorem subadditive (A B : Finset (Fin n)) :
    f.value (A ∪ B) ≤ f.value A + f.value B := by
  have h := f.union_le A B
  have h0 := f.nonnegative ∅
  linarith

end Objective

end ConsistentSubmodular

end

end

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

theorem physicalProbability_mem_unitInterval
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m)
    (hp : IsSimplex p) (e : Fin n) :
    0 ≤ physicalProbability cores p e ∧ physicalProbability cores p e ≤ 1 := by
  exact ⟨physicalProbability_nonnegative cores p hp.1 e,
    (physicalProbability_le_mass cores p hp.1 e).trans_eq hp.2⟩

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

open scoped BigOperators
open ConsistentSubmodular

theorem solution {n m : ℕ} (f : Objective n)
    (cores : Fin (m + 1) → Finset (Fin n)) (B : Finset (Fin n))
    (V : ℝ) (hV : 0 ≤ V) (hcore : ∀ i, f.value (cores i) ≤ V)
    (p q : Point m) (hp : IsSimplex p) (hq : IsSimplex q) :
    finiteExpectation p (f.onTypes cores B).value - V * (∑ i, |p i - q i|) ≤
      finiteExpectation (fun e => min (physicalProbability cores p e) (physicalProbability cores q e))
        (fun A => f.value (B ∪ A)) := by
  have hsing : ∀ i, (f.onTypes cores B).value {i}-(f.onTypes cores B).value ∅ ≤ V := by
    intro i
    rw [Objective.onTypes_singleton, Objective.onTypes_empty]
    have hh := f.subadditive B (cores i)
    linarith [hcore i]
  have hpc : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := fun i => ⟨hp.1 i, hp.coordinate_le_one i⟩
  have hqc : ∀ i, 0 ≤ q i ∧ q i ≤ 1 := fun i => ⟨hq.1 i, hq.coordinate_le_one i⟩
  have htype := (f.onTypes cores B).finiteExpectation_min_lower V hV hsing p q hpc hqc
  have hmin0 : ∀ i, 0 ≤ min (p i) (q i) := fun i => le_min (hp.1 i) (hq.1 i)
  have hmass : (∑ i, min (p i) (q i)) ≤ 1 :=
    (Finset.sum_le_sum (fun i _ => min_le_left _ _)).trans_eq hp.2
  have hlift := physical_multilinear_lift f cores B (fun i => min (p i) (q i)) hmin0 hmass
  have hsmall : ∀ e, 0 ≤ physicalProbability cores (fun i => min (p i) (q i)) e ∧
      physicalProbability cores (fun i => min (p i) (q i)) e ≤ 1 := by
    intro e
    exact ⟨physicalProbability_nonnegative cores _ hmin0 e,
      (physicalProbability_le_mass cores _ hmin0 e).trans hmass⟩
  have hlarge : ∀ e, 0 ≤ min (physicalProbability cores p e) (physicalProbability cores q e) ∧
      min (physicalProbability cores p e) (physicalProbability cores q e) ≤ 1 := by
    intro e
    exact ⟨le_min (physicalProbability_mem_unitInterval cores p hp e).1
      (physicalProbability_mem_unitInterval cores q hq e).1,
      (min_le_left _ _).trans (physicalProbability_mem_unitInterval cores p hp e).2⟩
  have hm := f.sampleAdd_mono_probability Finset.univ
    (physicalProbability cores (fun i => min (p i) (q i)))
    (fun e => min (physicalProbability cores p e) (physicalProbability cores q e))
    (fun e _ => hsmall e) (fun e _ => hlarge e)
    (fun e _ => physicalProbability_min_le cores p q e) B
  have hm' : finiteExpectation (physicalProbability cores (fun i => min (p i) (q i)))
      (fun A => f.value (B ∪ A)) ≤
      finiteExpectation (fun e => min (physicalProbability cores p e) (physicalProbability cores q e))
        (fun A => f.value (B ∪ A)) := by
    simpa only [sampleAdd, sampleExpectation_univ] using hm
  exact htype.trans (hlift.trans hm')

end
