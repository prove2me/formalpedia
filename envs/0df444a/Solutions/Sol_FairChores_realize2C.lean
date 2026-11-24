-- Prove2me | solution 1 for FairChores.realize2C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:26:31.374089+00:00
-- url     : https://prove2.me/submissions/044cae6c-77f1-4957-a6b9-bc34623218b8

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
import Theorems.Thm_FairChores_biU_twoC
import Theorems.Thm_FairChores_cbarSum_empty
import Theorems.Thm_FairChores_exists_outcome_of_preAlloc
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (c : Fin 2 → T → ℝ) (p : T → ℝ) (hp : ∀ t, 0 ≤ p t)
    (B0 B1 F : Finset T) (r0 r1 : ℝ)
    (hd01 : Disjoint B0 B1) (hdF0 : Disjoint F B0) (hdF1 : Disjoint F B1)
    (hcover : F ∪ (B0 ∪ B1) = Finset.univ)
    (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1) (hsum : r0 + r1 = ∑ t ∈ F, p t) :
    ∃ o : Outcome T 2, o.Valid p ∧
      cost (c 0) o 0 = cbarSum (c 0) p B0 + r0 ∧
      cost (c 1) o 1 = cbarSum (c 1) p B1 + r1 := by
  classical
  obtain ⟨o, hvalid, hcost⟩ :=
    exists_outcome_of_preAlloc ⟨![B0, B1], F, ![r0, r1]⟩ p c hp
      (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [hd01.symm])
      (by intro i; fin_cases i <;> simpa)
      (by
        show F ∪ Finset.univ.biUnion ![B0, B1] = Finset.univ
        rw [biU_twoC]
        simpa using hcover)
      (by intro i; fin_cases i <;> simpa)
      (by rw [Fin.sum_univ_two]; simpa using hsum)
  exact ⟨o, hvalid, by simpa using hcost 0, by simpa using hcost 1⟩
end FairChores
