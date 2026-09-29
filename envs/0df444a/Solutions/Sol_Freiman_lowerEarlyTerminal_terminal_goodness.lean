-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_terminal_goodness
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:50:10.994208+00:00
-- url     : https://prove2.me/submissions/030e58b8-58f8-4c1a-8a06-2ebae8d54f00

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic.Linarith

open Freiman

lemma compl_of_not (b : CertBound) (r s q : ℝ) (h : ¬ certBoundHolds b r s q) :
    certBoundHolds (lowerHistoryComplement b) r s q := by
  obtain ⟨lo, st, t⟩ := b
  cases lo <;> cases st <;> simp [certBoundHolds, lowerHistoryComplement] at h ⊢ <;> linarith

theorem solution (hp : LowerEarlyTerminalParameterLaws) (C : LowerEarlyTerminalCatalog) (p : LowerPair)
    (h27 : ¬ lowerA p 27) (h34 : ¬ lowerA p 34)
    (h : lowerEarlyTerminalRequiredSound C p 2) (ha : lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C 2))
    (hn : ∀ w : LowerPair, (lowerCover w).Nonempty)
    (hgood : ∀ l, lowerEarlyTerminalNative p l → (∀ req ∈ lowerEarlyTerminalGoodRequirements [] l, lowerEarlyTerminalAt p req.1 →
      lowerEarlyTerminalKindHolds p req.2) → lowerGood (lowerChild p l))
    (hanchors : lowerGood (lowerChild p ([3],[2])) ∧ lowerGood (lowerChild p ([2],[2]))) :
    lowerEarlyTerminalLabelsGood p (lowerEarlyTerminalTerminal (lowerEarlyTerminalPrimary p)) := by
  classical
  -- the actual early list is the terminal list selected by the A40 decision
  have hEL : lowerEarlyList p = lowerEarlyTerminalTerminal (lowerEarlyTerminalPrimary p) := by
    unfold lowerEarlyList lowerEarlyTerminalPrimary
    rw [if_neg h27, if_neg h34]
    by_cases h40 : lowerA p 40
    · rw [if_pos h40, decide_eq_true h40]
      rfl
    · rw [if_neg h40, decide_eq_false h40]
      rfl
  -- lifting a goodness requirement to a hypothesis list
  have hlift : ∀ (hyp : List CertBound) (l : LowerLabel) (req : LowerEarlyTerminalRequirement),
      req ∈ lowerEarlyTerminalGoodRequirements [] l →
      (hyp ++ req.1, req.2) ∈ lowerEarlyTerminalGoodRequirements hyp l := by
    intro hyp l req hreq
    unfold lowerEarlyTerminalGoodRequirements at hreq ⊢
    simp only [List.mem_flatMap] at hreq ⊢
    obtain ⟨⟨wide, norm⟩, hmem, hreq⟩ := hreq
    refine ⟨(wide, norm), hmem, ?_⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hreq ⊢
    rcases hreq with rfl | rfl <;> simp
  -- goodness of a native label whose goodness requirements (under hyp') are route requirements
  have hfrom : ∀ (hyp' : List CertBound) (l : LowerLabel), lowerEarlyTerminalAt p hyp' →
      (∀ x ∈ lowerEarlyTerminalGoodRequirements hyp' l, x ∈ lowerEarlyTerminalRequirements C 2) →
      lowerEarlyTerminalNative p l → lowerGood (lowerChild p l) := by
    intro hyp' l hat hsub hnat
    apply hgood l hnat
    intro req hreq hat1
    have hk := h _ (hsub _ (hlift hyp' l req hreq)) (by
      intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · exact hat b hb
      · exact hat1 b hb)
    exact hk
  have hreq2 : lowerEarlyTerminalRequirements C 2 = lowerEarlyTerminalTerminalRequirements C := by
    unfold lowerEarlyTerminalRequirements
    rw [if_neg (by norm_num)]
  -- ordinary labels
  have hord : ∀ l, (l ∈ lowerEarlyTerminalCommon ∨ l = lowerEarlyTerminalLast) →
      lowerEarlyTerminalNative p l → lowerGood (lowerChild p l) := by
    intro l hl hnat
    refine hfrom (lowerEarlyTerminalHyp C 2) l ha ?_ hnat
    intro x hx
    rw [hreq2]
    have hl' : l ∈ lowerEarlyTerminalCommon ++ [lowerEarlyTerminalLast] := by
      rcases hl with hl | rfl
      · exact List.mem_append_left _ hl
      · exact List.mem_append_right _ (List.mem_singleton_self _)
    have hxA : x ∈ (lowerEarlyTerminalCommon ++ [lowerEarlyTerminalLast]).flatMap fun l =>
        lowerEarlyTerminalCmp (lowerEarlyTerminalHyp C 2) l l ::
          lowerEarlyTerminalGoodRequirements (lowerEarlyTerminalHyp C 2) l :=
      List.mem_flatMap.2 ⟨l, hl', List.mem_cons_of_mem _ hx⟩
    simp only [lowerEarlyTerminalTerminalRequirements, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hxA)))))
  -- the middle label
  have hmid : lowerEarlyTerminalNative p (lowerEarlyTerminalMiddle (lowerEarlyTerminalPrimary p)) →
      lowerGood (lowerChild p (lowerEarlyTerminalMiddle (lowerEarlyTerminalPrimary p))) := by
    intro hnat
    have hD : lowerEarlyTerminalAt p [if lowerEarlyTerminalPrimary p then lowerEarlyTerminalD40 else
        lowerHistoryComplement lowerEarlyTerminalD40] := by
      unfold lowerEarlyTerminalPrimary
      by_cases h40 : lowerA p 40
      · rw [decide_eq_true h40]
        simp only [↓reduceIte]
        exact ((hp p).2.2.2.2.2.1).2 h40
      · rw [decide_eq_false h40]
        simp only [Bool.false_eq_true, ↓reduceIte]
        intro b hb
        rw [List.mem_singleton] at hb
        subst hb
        apply compl_of_not
        intro hD40
        apply h40
        apply ((hp p).2.2.2.2.2.1).1
        intro b hb
        rw [List.mem_singleton] at hb
        subst hb
        exact hD40
    refine hfrom (lowerEarlyTerminalHyp C 2 ++ [if lowerEarlyTerminalPrimary p then lowerEarlyTerminalD40 else
        lowerHistoryComplement lowerEarlyTerminalD40]) _ ?_ ?_ hnat
    · intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · exact ha b hb
      · exact hD b hb
    · intro x hx
      rw [hreq2]
      have hxC : x ∈ ([false,true] : List Bool).flatMap fun yes =>
          let h := lowerEarlyTerminalHyp C 2 ++ [if yes then lowerEarlyTerminalD40 else lowerHistoryComplement lowerEarlyTerminalD40]
          let m := lowerEarlyTerminalMiddle yes
          [lowerEarlyTerminalCmp h m m] ++ lowerEarlyTerminalGoodRequirements h m ++
            lowerEarlyTerminalContactRequirements h ([3,1,2],[3,1,1]) m ++
            lowerEarlyTerminalContactRequirements h m ([2,1,2],[3,1,1]) := by
        refine List.mem_flatMap.2 ⟨lowerEarlyTerminalPrimary p, ?_, ?_⟩
        · cases hb : lowerEarlyTerminalPrimary p <;> simp
        · simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inr hx))
      simp only [lowerEarlyTerminalTerminalRequirements, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hxC))))
  intro l hl
  refine ⟨?_, hn _⟩
  have hcase : l = ([3],[2]) ∨ l = ([2],[2]) ∨ (lowerEarlyTerminalNative p l ∧
      (l ∈ lowerEarlyTerminalCommon ∨ l = lowerEarlyTerminalLast ∨
        l = lowerEarlyTerminalMiddle (lowerEarlyTerminalPrimary p))) := by
    unfold lowerEarlyTerminalNative
    rw [hEL]
    revert l
    cases lowerEarlyTerminalPrimary p <;> decide
  rcases hcase with rfl | rfl | ⟨hnat, hl3⟩
  · exact hanchors.1
  · exact hanchors.2
  · rcases hl3 with h1 | h1 | h1
    · exact hord l (Or.inl h1) hnat
    · exact hord l (Or.inr h1) hnat
    · rw [h1] at hnat ⊢
      exact hmid hnat
