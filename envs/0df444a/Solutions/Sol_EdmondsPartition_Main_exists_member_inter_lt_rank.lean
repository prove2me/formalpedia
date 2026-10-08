-- Prove2me | solution 1 for EdmondsPartition.Main.exists_member_inter_lt_rank
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T16:01:40.740982+00:00
-- url     : https://prove2.me/submissions/2ac913d4-ddaa-4698-8415-f284caf5bf89

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace EdmondsWork

open WhitneyMatroid.RankIndep EdmondsPartition.Main

theorem exists_member_inter_lt_rank {α : Type*} [Fintype α] [DecidableEq α]
    (Indep : Finset α → Prop) (k : ℕ) (I : Fin k → Finset α)
    (hdisj : (Set.univ : Set (Fin k)).PairwiseDisjoint I) (x : α) (hx : ∀ i, x ∉ I i)
    (S : Finset α) (hxS : x ∈ S) (hS : (S.card : ℤ) ≤ (k : ℤ) * rankOfIndep Indep S) :
    ∃ i : Fin k, ((I i ∩ S).card : ℤ) < rankOfIndep Indep S := by
  by_contra hcon
  push Not at hcon
  have hdisj' : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint (fun i => I i ∩ S) := by
    intro i _ j _ hij
    exact (hdisj (Set.mem_univ i) (Set.mem_univ j) hij).mono Finset.inter_subset_left
      Finset.inter_subset_left
  have hcard := Finset.card_biUnion (s := Finset.univ) (t := fun i => I i ∩ S) hdisj'
  have hsub : Finset.univ.biUnion (fun i => I i ∩ S) ⊆ S.erase x := by
    intro a ha
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 ha
    obtain ⟨hiI, hiS⟩ := Finset.mem_inter.1 hi
    exact Finset.mem_erase.2 ⟨fun h => hx i (h ▸ hiI), hiS⟩
  have hle := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem hxS] at hle
  have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨x, hxS⟩
  have hsum : (k : ℤ) * rankOfIndep Indep S ≤ ∑ i : Fin k, ((I i ∩ S).card : ℤ) := by
    calc (k : ℤ) * rankOfIndep Indep S = ∑ _i : Fin k, rankOfIndep Indep S := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hcon i
  have hle' : ∑ i : Fin k, ((I i ∩ S).card : ℤ) ≤ (S.card : ℤ) - 1 := by
    have : ((∑ i : Fin k, (I i ∩ S).card : ℕ) : ℤ) ≤ ((S.card - 1 : ℕ) : ℤ) := by exact_mod_cast hle
    push_cast [Nat.cast_sub hpos] at this
    exact this
  linarith

end EdmondsWork

open WhitneyMatroid.RankIndep EdmondsPartition.Main

theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (Indep : Finset α → Prop) (k : ℕ) (I : Fin k → Finset α)
    (hdisj : (Set.univ : Set (Fin k)).PairwiseDisjoint I) (x : α) (hx : ∀ i, x ∉ I i)
    (S : Finset α) (hxS : x ∈ S) (hS : (S.card : ℤ) ≤ (k : ℤ) * rankOfIndep Indep S) :
    ∃ i : Fin k, ((I i ∩ S).card : ℤ) < rankOfIndep Indep S :=
  EdmondsWork.exists_member_inter_lt_rank Indep k I hdisj x hx S hxS hS

#print axioms solution
