-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_short_goodness
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:46:23.481265+00:00
-- url     : https://prove2.me/submissions/73910bb4-d972-401f-9971-3eca2d628a8b

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem solution (C : LowerEarlyTerminalCatalog) (p : LowerPair) (mode : ℕ) (hm : mode<2)
    (hb : if mode=0 then lowerA p 27 else ¬ lowerA p 27 ∧ lowerA p 34)
    (h : lowerEarlyTerminalRequiredSound C p mode) (ha : lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C mode))
    (hn : ∀ w : LowerPair, (lowerCover w).Nonempty)
    (hgood : ∀ l, lowerEarlyTerminalNative p l → (∀ req ∈ lowerEarlyTerminalGoodRequirements [] l, lowerEarlyTerminalAt p req.1 →
      lowerEarlyTerminalKindHolds p req.2) → lowerGood (lowerChild p l))
    (hanchors : lowerGood (lowerChild p ([3],[2])) ∧ lowerGood (lowerChild p ([2],[2]))) :
    lowerEarlyTerminalLabelsGood p (if mode=0 then lowerEarlyTerminalFirst else lowerEarlyTerminalSecond) := by
  -- the actual early list is the route list
  have hEL : lowerEarlyList p = (if mode=0 then lowerEarlyTerminalFirst else lowerEarlyTerminalSecond) := by
    rcases (by omega : mode = 0 ∨ mode = 1) with rfl | rfl
    · rw [if_pos rfl] at hb ⊢
      unfold lowerEarlyList
      rw [if_pos hb]
      rfl
    · have h10 : ¬ ((1:ℕ) = 0) := by norm_num
      rw [if_neg h10] at hb ⊢
      unfold lowerEarlyList
      rw [if_neg hb.1, if_pos hb.2]
      rfl
  -- interior labels: native, and their goodness requirements are route requirements
  have hint : ∀ l ∈ (if mode=0 then lowerEarlyTerminalFirst else lowerEarlyTerminalSecond).tail.dropLast,
      lowerGood (lowerChild p l) := by
    intro l hl
    apply hgood l
    · unfold lowerEarlyTerminalNative
      rw [hEL]
      exact hl
    · intro req hreq hat
      have hlift : (lowerEarlyTerminalHyp C mode ++ req.1, req.2) ∈
          lowerEarlyTerminalGoodRequirements (lowerEarlyTerminalHyp C mode) l := by
        unfold lowerEarlyTerminalGoodRequirements at hreq ⊢
        simp only [List.mem_flatMap] at hreq ⊢
        obtain ⟨⟨wide, norm⟩, hmem, hreq⟩ := hreq
        refine ⟨(wide, norm), hmem, ?_⟩
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hreq ⊢
        rcases hreq with rfl | rfl <;> simp
      have hmem : (lowerEarlyTerminalHyp C mode ++ req.1, req.2) ∈ lowerEarlyTerminalRequirements C mode := by
        unfold lowerEarlyTerminalRequirements
        rw [if_pos hm]
        simp only [lowerEarlyTerminalShortRequirements]
        exact List.mem_append_left _ (List.mem_flatMap.2 ⟨l, hl, List.mem_cons_of_mem _ hlift⟩)
      have hat' : lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C mode ++ req.1) := by
        intro b hb
        rcases List.mem_append.1 hb with hb | hb
        · exact ha b hb
        · exact hat b hb
      have hk := h _ hmem hat'
      exact hk
  intro l hl
  refine ⟨?_, hn _⟩
  have hcases : l = ([3],[2]) ∨ l = ([2],[2]) ∨
      l ∈ (if mode=0 then lowerEarlyTerminalFirst else lowerEarlyTerminalSecond).tail.dropLast := by
    split_ifs at hl ⊢ <;> revert l <;> decide
  rcases hcases with rfl | rfl | hl'
  · exact hanchors.1
  · exact hanchors.2
  · exact hint l hl'
