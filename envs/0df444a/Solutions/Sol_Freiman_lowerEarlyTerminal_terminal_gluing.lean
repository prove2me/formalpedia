-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_terminal_gluing
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:48:43.532716+00:00
-- url     : https://prove2.me/submissions/9fa27b9f-3b78-469f-a4b3-e79533d6ed58

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Topology.Order.IntermediateValue

open Freiman

/-- union of the covers of the children along a label list -/
def U (p : LowerPair) (ls : List LowerLabel) : Set ℝ :=
  {t : ℝ | ∃ l ∈ ls, t ∈ lowerCover (lowerChild p l)}

lemma U_cons (p : LowerPair) (a : LowerLabel) (ls : List LowerLabel) :
    U p (a :: ls) = lowerCover (lowerChild p a) ∪ U p ls := by
  ext t
  simp only [U, Set.mem_setOf_eq, Set.mem_union, List.mem_cons, exists_eq_or_imp]

lemma U_nil (p : LowerPair) : U p [] = ∅ := by
  ext t
  simp [U]

lemma step (p : LowerPair) (a : LowerLabel) (ls : List LowerLabel)
    (h : IsPreconnected (U p ls)) (hx : ∃ x ∈ lowerCover (lowerChild p a), x ∈ U p ls) :
    IsPreconnected (U p (a :: ls)) := by
  rw [U_cons]
  obtain ⟨x, hxa, hxU⟩ := hx
  exact IsPreconnected.union x hxa hxU isPreconnected_Icc h

lemma mem_U (p : LowerPair) (ls : List LowerLabel) (m : LowerLabel) (hm : m ∈ ls) (x : ℝ)
    (hx : x ∈ lowerCover (lowerChild p m)) : x ∈ U p ls := ⟨m, hm, hx⟩

lemma glue (p : LowerPair) (l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 : LowerLabel)
    (c01 : lowerEarlyTerminalContact p l0 l1) (c12 : lowerEarlyTerminalContact p l1 l2)
    (c23 : lowerEarlyTerminalContact p l2 l3) (c34 : lowerEarlyTerminalContact p l3 l4)
    (c45 : lowerEarlyTerminalContact p l4 l5) (c56 : lowerEarlyTerminalContact p l5 l6)
    (c67 : lowerEarlyTerminalContact p l6 l7) (c78 : lowerEarlyTerminalContact p l7 l8)
    (c8 : lowerEarlyTerminalContact p l8 l9 ∨ lowerEarlyTerminalContact p l8 l10)
    (c910 : lowerEarlyTerminalContact p l9 l10) (c1011 : lowerEarlyTerminalContact p l10 l11)
    (c1112 : lowerEarlyTerminalContact p l11 l12) (c1213 : lowerEarlyTerminalContact p l12 l13)
    (c1314 : lowerEarlyTerminalContact p l13 l14)
    (c14 : (lowerCover (lowerChild p l14) ∩ (lowerCover (lowerChild p l15) ∪ lowerCover (lowerChild p l16))).Nonempty)
    (c1516 : lowerEarlyTerminalContact p l15 l16) :
    IsPreconnected (U p [l0,l1,l2,l3,l4,l5,l6,l7,l8,l9,l10,l11,l12,l13,l14,l15,l16]) := by
  have s16 : IsPreconnected (U p [l16]) := by
    rw [U_cons, U_nil, Set.union_empty]
    exact isPreconnected_Icc
  have s15 : IsPreconnected (U p [l15,l16]) := by
    obtain ⟨x, hx1, hx2⟩ := c1516
    exact step p _ _ s16 ⟨x, hx1, mem_U p _ l16 (by simp) x hx2⟩
  have s14 : IsPreconnected (U p [l14,l15,l16]) := by
    obtain ⟨x, hx1, hx2⟩ := c14
    refine step p _ _ s15 ⟨x, hx1, ?_⟩
    rw [U_cons, U_cons, U_nil, Set.union_empty]
    exact hx2
  have s13 : IsPreconnected (U p [l13,l14,l15,l16]) := by
    obtain ⟨x, hx1, hx2⟩ := c1314
    exact step p _ _ s14 ⟨x, hx1, mem_U p _ l14 (by simp) x hx2⟩
  have s12 : IsPreconnected (U p [l12,l13,l14,l15,l16]) := by
    obtain ⟨x, hx1, hx2⟩ := c1213
    exact step p _ _ s13 ⟨x, hx1, mem_U p _ l13 (by simp) x hx2⟩
  have s11 : IsPreconnected (U p [l11,l12,l13,l14,l15,l16]) := by
    obtain ⟨x, hx1, hx2⟩ := c1112
    exact step p _ _ s12 ⟨x, hx1, mem_U p _ l12 (by simp) x hx2⟩
  have s10 : IsPreconnected (U p [l10,l11,l12,l13,l14,l15,l16]) := by
    obtain ⟨x, hx1, hx2⟩ := c1011
    exact step p _ _ s11 ⟨x, hx1, mem_U p _ l11 (by simp) x hx2⟩
  have s9 : IsPreconnected (U p [l9,l10,l11,l12,l13,l14,l15,l16]) := by
    obtain ⟨x, hx1, hx2⟩ := c910
    exact step p _ _ s10 ⟨x, hx1, mem_U p _ l10 (by simp) x hx2⟩
  have s8 : IsPreconnected (U p [l8,l9,l10,l11,l12,l13,l14,l15,l16]) := by
    rcases c8 with ⟨x, hx1, hx2⟩ | ⟨x, hx1, hx2⟩
    · exact step p _ _ s9 ⟨x, hx1, mem_U p _ l9 (by simp) x hx2⟩
    · exact step p _ _ s9 ⟨x, hx1, mem_U p _ l10 (by simp) x hx2⟩
  have s7 : IsPreconnected (U p [l7,l8,l9,l10,l11,l12,l13,l14,l15,l16]) := by
    obtain ⟨x, hx1, hx2⟩ := c78
    exact step p _ _ s8 ⟨x, hx1, mem_U p _ l8 (by simp) x hx2⟩
  have s6 : IsPreconnected (U p [l6,l7,l8,l9,l10,l11,l12,l13,l14,l15,l16]) := by
    obtain ⟨x, hx1, hx2⟩ := c67
    exact step p _ _ s7 ⟨x, hx1, mem_U p _ l7 (by simp) x hx2⟩
  have s5 : IsPreconnected (U p [l5,l6,l7,l8,l9,l10,l11,l12,l13,l14,l15,l16]) := by
    obtain ⟨x, hx1, hx2⟩ := c56
    exact step p _ _ s6 ⟨x, hx1, mem_U p _ l6 (by simp) x hx2⟩
  have s4 : IsPreconnected (U p [l4,l5,l6,l7,l8,l9,l10,l11,l12,l13,l14,l15,l16]) := by
    obtain ⟨x, hx1, hx2⟩ := c45
    exact step p _ _ s5 ⟨x, hx1, mem_U p _ l5 (by simp) x hx2⟩
  have s3 : IsPreconnected (U p [l3,l4,l5,l6,l7,l8,l9,l10,l11,l12,l13,l14,l15,l16]) := by
    obtain ⟨x, hx1, hx2⟩ := c34
    exact step p _ _ s4 ⟨x, hx1, mem_U p _ l4 (by simp) x hx2⟩
  have s2 : IsPreconnected (U p [l2,l3,l4,l5,l6,l7,l8,l9,l10,l11,l12,l13,l14,l15,l16]) := by
    obtain ⟨x, hx1, hx2⟩ := c23
    exact step p _ _ s3 ⟨x, hx1, mem_U p _ l3 (by simp) x hx2⟩
  have s1 : IsPreconnected (U p [l1,l2,l3,l4,l5,l6,l7,l8,l9,l10,l11,l12,l13,l14,l15,l16]) := by
    obtain ⟨x, hx1, hx2⟩ := c12
    exact step p _ _ s2 ⟨x, hx1, mem_U p _ l2 (by simp) x hx2⟩
  obtain ⟨x, hx1, hx2⟩ := c01
  exact step p _ _ s1 ⟨x, hx1, mem_U p _ l1 (by simp) x hx2⟩

theorem solution (p : LowerPair) (primary : Bool) (h : lowerEarlyTerminalTerminalData p primary) :
    lowerEarlyTerminalListGeometry p (lowerEarlyTerminalTerminal primary) := by
  obtain ⟨hg, hcon, hm1, hm2, hd, hl, hu⟩ := h
  refine ⟨fun l hl => (hg l hl).1, ?_, ?_, ?_⟩
  · have c01 := hcon _ (by decide : ((([3],[2]) : LowerLabel),(([3,1,2],[3,1,2]) : LowerLabel)) ∈ lowerEarlyTerminalContacts)
    have c12 := hcon _ (by decide : ((([3,1,2],[3,1,2]) : LowerLabel),(([3,1,2],[3,1,1]) : LowerLabel)) ∈ lowerEarlyTerminalContacts)
    have c45 := hcon _ (by decide : ((([2,1,2],[3,1,1]) : LowerLabel),(([3,1,2],[3,2]) : LowerLabel)) ∈ lowerEarlyTerminalContacts)
    have c56 := hcon _ (by decide : ((([3,1,2],[3,2]) : LowerLabel),(([3,1,2],[3,3]) : LowerLabel)) ∈ lowerEarlyTerminalContacts)
    have c67 := hcon _ (by decide : ((([3,1,2],[3,3]) : LowerLabel),(([2,1,2],[3,2]) : LowerLabel)) ∈ lowerEarlyTerminalContacts)
    have c78 := hcon _ (by decide : ((([2,1,2],[3,2]) : LowerLabel),(([1,1,1,2],[3,1,1]) : LowerLabel)) ∈ lowerEarlyTerminalContacts)
    have c910 := hcon _ (by decide : ((([2,1,1,2],[3,1,1]) : LowerLabel),(([1,1,1,2],[3,2]) : LowerLabel)) ∈ lowerEarlyTerminalContacts)
    have c1011 := hcon _ (by decide : ((([1,1,1,2],[3,2]) : LowerLabel),(([1,1,1,2],[3,3]) : LowerLabel)) ∈ lowerEarlyTerminalContacts)
    have c1112 := hcon _ (by decide : ((([1,1,1,2],[3,3]) : LowerLabel),(([2,1,1,2],[3,2]) : LowerLabel)) ∈ lowerEarlyTerminalContacts)
    have c1213 := hcon _ (by decide : ((([2,1,1,2],[3,2]) : LowerLabel),(([3,1,1,2],[3,2]) : LowerLabel)) ∈ lowerEarlyTerminalContacts)
    have c1314 := hcon _ (by decide : ((([3,1,1,2],[3,2]) : LowerLabel),(([2,1,1,2],[3,3]) : LowerLabel)) ∈ lowerEarlyTerminalContacts)
    have key := glue p ([3],[2]) ([3,1,2],[3,1,2]) ([3,1,2],[3,1,1]) (lowerEarlyTerminalMiddle primary)
      ([2,1,2],[3,1,1]) ([3,1,2],[3,2]) ([3,1,2],[3,3]) ([2,1,2],[3,2]) ([1,1,1,2],[3,1,1])
      ([2,1,1,2],[3,1,1]) ([1,1,1,2],[3,2]) ([1,1,1,2],[3,3]) ([2,1,1,2],[3,2]) ([3,1,1,2],[3,2])
      ([2,1,1,2],[3,3]) lowerEarlyTerminalLast ([2],[2])
      c01 c12 hm1 hm2 c45 c56 c67 c78 hd c910 c1011 c1112 c1213 c1314 hu hl
    exact key
  · intro t ht
    exact ⟨([3],[2]), by cases primary <;> decide, ht⟩
  · intro t ht
    exact ⟨([2],[2]), by cases primary <;> decide, ht⟩
