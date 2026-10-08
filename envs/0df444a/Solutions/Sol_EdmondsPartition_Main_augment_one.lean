-- Prove2me | solution 1 for EdmondsPartition.Main.augment_one
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T16:01:48.041956+00:00
-- url     : https://prove2.me/submissions/aa0ea1b8-4798-49fd-b540-b5135047644c

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic
import Theorems.Thm_EdmondsPartition_Main_partition_of_counting
import Theorems.Thm_EdmondsPartition_Main_span_facts

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


open WhitneyMatroid.RankIndep EdmondsPartition.Main

theorem solution {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop)
    (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (k : ℕ)
    (hspan : ∀ S : Finset α, IsSpan Indep S → (S.card : ℤ) ≤ (k : ℤ) * rankOfIndep Indep S)
    (I : Fin k → Finset α) (hI : ∀ i, Indep (I i))
    (hdisj : (Set.univ : Set (Fin k)).PairwiseDisjoint I) (x : α) (hx : ∀ i, x ∉ I i) :
    ∃ I' : Fin k → Finset α, (∀ i, Indep (I' i)) ∧ (Set.univ : Set (Fin k)).PairwiseDisjoint I' ∧
      Finset.univ.biUnion I' = insert x (Finset.univ.biUnion I) :=
  by
  have hcount : ∀ J : Finset α, (J.card : ℤ) ≤ (k : ℤ) * rankOfIndep Indep J := by
    intro J
    obtain ⟨ha, hb, hc⟩ := span_facts Indep h1 h2 h0 J
    have hJ : J ⊆ spanOf Indep J := fun e he => (ha e).2 (by rw [Finset.insert_eq_of_mem he])
    calc (J.card : ℤ) ≤ (spanOf Indep J).card := by exact_mod_cast Finset.card_le_card hJ
      _ ≤ (k : ℤ) * rankOfIndep Indep (spanOf Indep J) := hspan _ hb
      _ = (k : ℤ) * rankOfIndep Indep J := by rw [hc]
  exact partition_of_counting Indep h1 h2 h0 k _ (fun J _ => hcount J)

#print axioms solution
