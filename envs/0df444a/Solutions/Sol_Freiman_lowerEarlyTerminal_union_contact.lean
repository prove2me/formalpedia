-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_union_contact
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:51:01.024212+00:00
-- url     : https://prove2.me/submissions/07aac165-65c7-4fb6-9033-8f9a5ee7f27c

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic.Linarith

open Freiman

theorem solution (p : LowerPair) (a b c : LowerLabel)
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true)
    (hbc : lowerEarlyTerminalContact p b c)
    (hforward : lowerEarlyTerminalEndpoint p (section14LabelWords b) false ≤ lowerEarlyTerminalEndpoint p (section14LabelWords a) true ∨
      lowerEarlyTerminalEndpoint p (section14LabelWords c) false ≤ lowerEarlyTerminalEndpoint p (section14LabelWords a) true)
    (hreverse : lowerEarlyTerminalEndpoint p (section14LabelWords a) false ≤ lowerEarlyTerminalEndpoint p (section14LabelWords c) true) :
    (lowerCover (lowerChild p a) ∩ (lowerCover (lowerChild p b) ∪ lowerCover (lowerChild p c))).Nonempty := by
  have key : ∀ (l : LowerLabel) (u : Bool), lowerEarlyTerminalEndpoint p (section14LabelWords l) u =
      (if lowerHistoryCommonOdd (lowerNormalize p) ⟨([],[]),(false,false)⟩ then -1 else 1) *
        lowerEndpoint (lowerChild p l) (u.xor (lowerHistoryCommonOdd (lowerNormalize p) ⟨([],[]),(false,false)⟩)) := by
    intro l u
    rfl
  simp only [key] at hforward hreverse
  -- endpoints of the three children
  set a0 := lowerEndpoint (lowerChild p a) false with ha0
  set a1 := lowerEndpoint (lowerChild p a) true with ha1
  set b0 := lowerEndpoint (lowerChild p b) false with hb0
  set b1 := lowerEndpoint (lowerChild p b) true with hb1
  set c0 := lowerEndpoint (lowerChild p c) false with hc0
  set c1 := lowerEndpoint (lowerChild p c) true with hc1
  have hoa : a0 ≤ a1 := ho _
  have hob : b0 ≤ b1 := ho _
  have hoc : c0 ≤ c1 := ho _
  obtain ⟨x, hxb, hxc⟩ := hbc
  rw [lowerCover, Set.mem_Icc] at hxb hxc
  have hb0c1 : b0 ≤ c1 := le_trans hxb.1 hxc.2
  have hc0b1 : c0 ≤ b1 := le_trans hxc.1 hxb.2
  -- an intersection point with b or with c
  have hAB : a0 ≤ b1 → b0 ≤ a1 → (lowerCover (lowerChild p a) ∩ (lowerCover (lowerChild p b) ∪ lowerCover (lowerChild p c))).Nonempty := by
    intro h h'
    refine ⟨max a0 b0, Set.mem_Icc.2 ⟨le_max_left _ _, max_le hoa h'⟩, Or.inl (Set.mem_Icc.2 ⟨le_max_right _ _, max_le h hob⟩)⟩
  have hAC : a0 ≤ c1 → c0 ≤ a1 → (lowerCover (lowerChild p a) ∩ (lowerCover (lowerChild p b) ∪ lowerCover (lowerChild p c))).Nonempty := by
    intro h h'
    refine ⟨max a0 c0, Set.mem_Icc.2 ⟨le_max_left _ _, max_le hoa h'⟩, Or.inr (Set.mem_Icc.2 ⟨le_max_right _ _, max_le h hoc⟩)⟩
  generalize lowerHistoryCommonOdd (lowerNormalize p) ⟨([],[]),(false,false)⟩ = s at hforward hreverse
  cases s
  · simp at hforward hreverse
    -- hforward : b0 ≤ a1 ∨ c0 ≤ a1 ; hreverse : a0 ≤ c1
    rcases hforward with h | h
    · by_cases hab : a0 ≤ b1
      · exact hAB hab h
      · push_neg at hab
        exact hAC hreverse (by linarith)
    · exact hAC hreverse h
  · simp at hforward hreverse
    -- hforward : a0 ≤ b1 ∨ a0 ≤ c1 ; hreverse : c0 ≤ a1
    rcases hforward with h | h
    · by_cases hab : b0 ≤ a1
      · exact hAB h hab
      · push_neg at hab
        exact hAC (by linarith) hreverse
    · exact hAC h hreverse
