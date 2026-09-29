-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_requirements_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:41:13.084497+00:00
-- url     : https://prove2.me/submissions/5e69e40b-adde-4a34-9b86-2ead8975488c

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

lemma good_kind (hyp : List CertBound) (l : LowerLabel) :
    ∀ x ∈ lowerEarlyTerminalGoodRequirements hyp l,
      ∃ u hi v hj st, x.2 = LowerEarlyTerminalKind.compare u hi v hj st := by
  intro x hx
  unfold lowerEarlyTerminalGoodRequirements at hx
  simp only [List.mem_flatMap] at hx
  obtain ⟨⟨wide, norm⟩, -, hx⟩ := hx
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> exact ⟨_, _, _, _, _, rfl⟩

lemma contact_kind (hyp : List CertBound) (a b : LowerLabel) :
    ∀ x ∈ lowerEarlyTerminalContactRequirements hyp a b,
      ∃ u hi v hj st, x.2 = LowerEarlyTerminalKind.compare u hi v hj st := by
  intro x hx
  simp only [lowerEarlyTerminalContactRequirements, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> exact ⟨_, _, _, _, _, rfl⟩

lemma short_kind (C : LowerEarlyTerminalCatalog) (m : ℕ) :
    ∀ x ∈ lowerEarlyTerminalShortRequirements C m,
      ∃ u hi v hj st, x.2 = LowerEarlyTerminalKind.compare u hi v hj st := by
  intro x hx
  simp only [lowerEarlyTerminalShortRequirements] at hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨l, -, hx⟩ := List.mem_flatMap.1 hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, _, _, _, _, rfl⟩
    · exact good_kind _ _ x hx
  · obtain ⟨⟨a, b⟩, -, hx⟩ := List.mem_flatMap.1 hx
    exact contact_kind _ _ _ x hx

lemma terminal_kind (C : LowerEarlyTerminalCatalog) :
    ∀ x ∈ lowerEarlyTerminalTerminalRequirements C,
      (∃ u hi v hj st, x.2 = LowerEarlyTerminalKind.compare u hi v hj st) ∨
      (∃ j, x = (lowerEarlyTerminalHyp C 2, LowerEarlyTerminalKind.unionCase j)) := by
  intro x hx
  simp only [lowerEarlyTerminalTerminalRequirements] at hx
  rcases List.mem_append.1 hx with hx | hx
  · left
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with hx | hx
      · rcases List.mem_append.1 hx with hx | hx
        · rcases List.mem_append.1 hx with hx | hx
          · rcases List.mem_append.1 hx with hx | hx
            · obtain ⟨l, -, hx⟩ := List.mem_flatMap.1 hx
              rcases List.mem_cons.1 hx with rfl | hx
              · exact ⟨_, _, _, _, _, rfl⟩
              · exact good_kind _ _ x hx
            · obtain ⟨⟨a, b⟩, -, hx⟩ := List.mem_flatMap.1 hx
              exact contact_kind _ _ _ x hx
          · obtain ⟨yes, -, hx⟩ := List.mem_flatMap.1 hx
            try dsimp only at hx
            rcases List.mem_append.1 hx with hx | hx
            · rcases List.mem_append.1 hx with hx | hx
              · rcases List.mem_append.1 hx with hx | hx
                · rw [List.mem_singleton] at hx
                  subst hx
                  exact ⟨_, _, _, _, _, rfl⟩
                · exact good_kind _ _ x hx
              · exact contact_kind _ _ _ x hx
            · exact contact_kind _ _ _ x hx
        · obtain ⟨yes, -, hx⟩ := List.mem_flatMap.1 hx
          try dsimp only at hx
          exact contact_kind _ _ _ x hx
      · exact contact_kind _ _ _ x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact ⟨_, _, _, _, _, rfl⟩
  · right
    obtain ⟨j, -, hj⟩ := List.mem_map.1 hx
    exact ⟨j, hj.symm⟩

theorem solution (he : LowerEarlyTerminalEndpointLaw) (hg : LowerEarlyTerminalGreaterLaw)
    (C : LowerEarlyTerminalCatalog) (p : LowerPair) (mode : ℕ)
    (hm : lowerEarlyTerminalMatches p C)
    (hr : certRectangleMem C.rectangle (lowerEarlyTerminalR p) (lowerEarlyTerminalS p))
    (hv : lowerEarlyTerminalRequirementBinding C mode) (hs : lowerEarlyTerminalGoalsSound C)
    (hcmp : ∀ u hi v hj strict,
      (∀ b ∈ lowerEarlyTerminalCompare C u hi v hj strict, lowerEarlyTerminalAt p b.1 →
        section14ComparisonHolds b.2 (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) (lowerEarlyTerminalQ p)) →
      lowerEarlyTerminalKindHolds p (.compare u hi v hj strict))
    (hun : (∀ b ∈ lowerEarlyTerminalUnionCases C, lowerEarlyTerminalAt p b.1 →
        section14ComparisonHolds b.2 (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) (lowerEarlyTerminalQ p)) →
      lowerEarlyTerminalUnionHolds p) : lowerEarlyTerminalRequiredSound C p mode := by
  -- branch soundness at the actual parameters for every bound requirement
  have hgoal : ∀ req ∈ lowerEarlyTerminalRequirements C mode, lowerEarlyTerminalAt p req.1 →
      ∀ b ∈ lowerEarlyTerminalBranches C req.2, lowerEarlyTerminalAt p b.1 →
        section14ComparisonHolds b.2 (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) (lowerEarlyTerminalQ p) := by
    intro req hreq hat b hb hb1
    obtain ⟨g, hg, hkind, hfin⟩ := hv req hreq
    have hprem : section14Holds (lowerEarlyTerminalBoundsAt C g.premises)
        (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) (lowerEarlyTerminalQ p) := by
      intro x hx
      apply hat
      have : x ∈ (lowerEarlyTerminalBoundsAt C g.premises).toFinset := List.mem_toFinset.2 hx
      rw [hfin] at this
      exact List.mem_toFinset.1 this
    exact hs _ _ _ hr g hg hprem b (by rw [hkind]; exact hb) hb1
  intro req hreq hat
  rcases hk : req.2 with ⟨u, hi, v, hj, strict⟩ | id | j | j
  · apply hcmp
    intro b hb hb1
    exact hgoal req hreq hat b (by rw [hk]; exact hb) hb1
  · trivial
  · have hmode : ¬ mode < 2 := by
      intro hlt
      have hx := hreq
      unfold lowerEarlyTerminalRequirements at hx
      rw [if_pos hlt] at hx
      obtain ⟨u, hi, v, hj, st, hc⟩ := short_kind C mode req hx
      rw [hk] at hc
      cases hc
    have hTR : lowerEarlyTerminalRequirements C mode = lowerEarlyTerminalTerminalRequirements C := by
      unfold lowerEarlyTerminalRequirements
      rw [if_neg hmode]
    have hreq1 : req.1 = lowerEarlyTerminalHyp C 2 := by
      have hx := hreq
      rw [hTR] at hx
      rcases terminal_kind C req hx with ⟨u, hi, v, hj, st, hc⟩ | ⟨j', hj'⟩
      · rw [hk] at hc
        cases hc
      · rw [hj']
    have hhyp : lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C 2) := by
      rw [← hreq1]
      exact hat
    show lowerEarlyTerminalUnionHolds p
    apply hun
    intro b hb
    obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hb
    have hreq' : (lowerEarlyTerminalHyp C 2, LowerEarlyTerminalKind.unionCase j') ∈
        lowerEarlyTerminalRequirements C mode := by
      rw [hTR]
      simp only [lowerEarlyTerminalTerminalRequirements, List.mem_append]
      exact Or.inr (List.mem_map.2 ⟨j', List.mem_range.2 hj', rfl⟩)
    refine hgoal _ hreq' hhyp (lowerEarlyTerminalUnionCases C)[j'] ?_
    show _ ∈ [(lowerEarlyTerminalUnionCases C)[j']?.getD ([],.impossible)]
    rw [List.getElem?_eq_getElem hj']
    simp
  · trivial
