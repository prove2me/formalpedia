-- Prove2me | solution 1 for ChromaticReconstruction.card_rankPartitions_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:40:47.105705+00:00
-- url     : https://prove2.me/submissions/d7c7e14c-74a8-43ff-aefe-e6a1bf7bf286

import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_CountingUpper
import Theorems.Thm_ChromaticReconstruction_bigParts_facts
import Theorems.Thm_ChromaticReconstruction_parts_eq_of_bigParts_eq
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution (k t : ℕ) :
    Fintype.card {μ : Nat.Partition k // k - t ≤ Multiset.card μ.parts} ≤ (t + 1) ^ (t + 2) := by
  let f : {μ : Nat.Partition k // k - t ≤ Multiset.card μ.parts} → (Fin (t + 2) → Fin (t + 1)) :=
    fun μ i => ⟨Multiset.count (i : ℕ) (bigParts μ.1),
      Nat.lt_succ_of_le ((Multiset.count_le_card _ _).trans (bigParts_facts μ.2).1)⟩
  have hf : Function.Injective f := by
    intro μ ν h
    apply Subtype.ext
    apply parts_eq_of_bigParts_eq
    ext a
    by_cases ha : a < t + 2
    · have := congrFun h ⟨a, ha⟩
      simp only [f, Fin.mk.injEq] at this
      exact this
    · have h1 : a ∉ bigParts μ.1 := fun hm => by have := (bigParts_facts μ.2).2 a hm; omega
      have h2 : a ∉ bigParts ν.1 := fun hm => by have := (bigParts_facts ν.2).2 a hm; omega
      rw [Multiset.count_eq_zero_of_notMem h1, Multiset.count_eq_zero_of_notMem h2]
  have := Fintype.card_le_of_injective f hf
  simpa using this
end ChromaticReconstruction
