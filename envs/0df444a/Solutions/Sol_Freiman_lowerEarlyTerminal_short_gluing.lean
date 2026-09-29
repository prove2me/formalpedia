-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_short_gluing
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:44:53.802008+00:00
-- url     : https://prove2.me/submissions/f608f577-4ad1-4c7e-a593-e58745f03b3b

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Topology.Order.IntermediateValue

open Freiman

lemma union_cons (p : LowerPair) (a : LowerLabel) (ls : List LowerLabel) :
    {t : ℝ | ∃ l ∈ a :: ls, t ∈ lowerCover (lowerChild p l)} =
      lowerCover (lowerChild p a) ∪ {t : ℝ | ∃ l ∈ ls, t ∈ lowerCover (lowerChild p l)} := by
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_union, List.mem_cons, exists_eq_or_imp]

lemma union_nil (p : LowerPair) :
    {t : ℝ | ∃ l ∈ ([] : List LowerLabel), t ∈ lowerCover (lowerChild p l)} = ∅ := by
  ext t
  simp

lemma chain_preconnected (p : LowerPair) : ∀ ls : List LowerLabel,
    ls.IsChain (lowerEarlyTerminalContact p) →
    IsPreconnected {t : ℝ | ∃ l ∈ ls, t ∈ lowerCover (lowerChild p l)}
  | [], _ => by
      rw [union_nil]
      exact isPreconnected_empty
  | [a], _ => by
      rw [union_cons, union_nil, Set.union_empty]
      exact isPreconnected_Icc
  | a :: b :: rest, hc => by
      rw [List.isChain_cons_cons] at hc
      obtain ⟨x, hxa, hxb⟩ := hc.1
      have ih := chain_preconnected p (b :: rest) hc.2
      rw [union_cons]
      refine IsPreconnected.union x hxa ?_ isPreconnected_Icc ih
      exact ⟨b, List.mem_cons_self .., hxb⟩

lemma geometry_of_data (p : LowerPair) (ls : List LowerLabel) (h : lowerEarlyTerminalShortData p ls)
    (h1 : ([3],[2]) ∈ ls) (h2 : ([2],[2]) ∈ ls) : lowerEarlyTerminalListGeometry p ls := by
  obtain ⟨hg, hc⟩ := h
  refine ⟨fun l hl => (hg l hl).1, chain_preconnected p ls hc, ?_, ?_⟩
  · intro t ht
    exact ⟨_, h1, ht⟩
  · intro t ht
    exact ⟨_, h2, ht⟩

theorem solution (p : LowerPair) (mode : ℕ) (hm : mode<2)
    (h : lowerEarlyTerminalShortData p (if mode=0 then lowerEarlyTerminalFirst else lowerEarlyTerminalSecond)) :
    lowerEarlyTerminalListGeometry p (if mode=0 then lowerEarlyTerminalFirst else lowerEarlyTerminalSecond) := by
  apply geometry_of_data p _ h
  · split_ifs <;> decide
  · split_ifs <;> decide
