-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_terminal_contacts
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:47:56.316355+00:00
-- url     : https://prove2.me/submissions/6d8f10ff-bc45-40df-9d64-361877f995f3

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic.Linarith

open Freiman

lemma compl_of_not (b : CertBound) (r s q : ℝ) (h : ¬ certBoundHolds b r s q) :
    certBoundHolds (lowerHistoryComplement b) r s q := by
  obtain ⟨lo, st, t⟩ := b
  cases lo <;> cases st <;> simp [certBoundHolds, lowerHistoryComplement] at h ⊢ <;> linarith

lemma at_compl (p : LowerPair) (b : CertBound) (h : ¬ lowerEarlyTerminalAt p [b]) :
    lowerEarlyTerminalAt p [lowerHistoryComplement b] := by
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  apply compl_of_not
  intro hb
  apply h
  intro y hy
  rw [List.mem_singleton] at hy
  subst hy
  exact hb

lemma equalCases_ne_nil (Cx : LowerHistoryContext) (w : LowerPair) (u : Bool) :
    section14EqualCases Cx w u ≠ [] := by
  intro hnil
  unfold section14EqualCases at hnil
  split_ifs at hnil <;> simp [section14NormalCases] at hnil <;> split_ifs at hnil <;> simp at hnil

lemma endpointCases_ne_nil (Cx : LowerHistoryContext) (w : LowerPair) (u : Bool) :
    section14EndpointCases Cx w u ≠ [] := by
  unfold section14EndpointCases
  split_ifs with h
  · exact equalCases_ne_nil _ _ _
  · intro hnil
    simp only [section14NormalCases, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_eq_nil_iff, List.map_eq_nil_iff] at hnil
    obtain ⟨h1, -⟩ := hnil
    split_ifs at h1 with h2
    all_goals first | exact equalCases_ne_nil _ _ _ h1 | exact List.cons_ne_nil _ _ h1

lemma unionCases_pos (C : LowerEarlyTerminalCatalog) : 0 < (lowerEarlyTerminalUnionCases C).length := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _
    (endpointCases_ne_nil (lowerEarlyTerminalContext C) ([2,1,1,2],[3,3]) true)
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _
    (endpointCases_ne_nil (lowerEarlyTerminalContext C) ([2,1,1,3],[3,3]) false)
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _
    (endpointCases_ne_nil (lowerEarlyTerminalContext C) ([2],[2]) false)
  apply List.length_pos_of_mem
  unfold lowerEarlyTerminalUnionCases
  exact List.mem_flatMap.2 ⟨a, ha, List.mem_flatMap.2 ⟨b, hb, List.mem_map.2 ⟨c, hc, rfl⟩⟩⟩

theorem solution (hp : LowerEarlyTerminalParameterLaws) (C : LowerEarlyTerminalCatalog) (p : LowerPair)
    (h : lowerEarlyTerminalRequiredSound C p 2) (ha : lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C 2))
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true)
    (hcontact : ∀ a b, lowerEarlyTerminalKindHolds p (.compare (section14LabelWords a) true (section14LabelWords b) false false) →
      lowerEarlyTerminalKindHolds p (.compare (section14LabelWords b) true (section14LabelWords a) false false) →
      lowerEarlyTerminalContact p a b)
    (hu : ∀ a b c, lowerEarlyTerminalContact p b c →
      (lowerEarlyTerminalEndpoint p (section14LabelWords b) false ≤ lowerEarlyTerminalEndpoint p (section14LabelWords a) true ∨
        lowerEarlyTerminalEndpoint p (section14LabelWords c) false ≤ lowerEarlyTerminalEndpoint p (section14LabelWords a) true) →
      lowerEarlyTerminalEndpoint p (section14LabelWords a) false ≤ lowerEarlyTerminalEndpoint p (section14LabelWords c) true →
      (lowerCover (lowerChild p a) ∩ (lowerCover (lowerChild p b) ∪ lowerCover (lowerChild p c))).Nonempty)
    (hl : lowerEarlyTerminalLabelsGood p (lowerEarlyTerminalTerminal (lowerEarlyTerminalPrimary p))) :
    lowerEarlyTerminalTerminalData p (lowerEarlyTerminalPrimary p) := by
  classical
  have hreq2 : lowerEarlyTerminalRequirements C 2 = lowerEarlyTerminalTerminalRequirements C := by
    unfold lowerEarlyTerminalRequirements
    rw [if_neg (by norm_num)]
  have hK : ∀ x ∈ lowerEarlyTerminalTerminalRequirements C, lowerEarlyTerminalAt p x.1 →
      lowerEarlyTerminalKindHolds p x.2 := by
    intro x hx
    apply h x
    rw [hreq2]
    exact hx
  -- contacts from a pair of route requirements under a hypothesis list that holds
  have hC : ∀ (hyp' : List CertBound) (a b : LowerLabel), lowerEarlyTerminalAt p hyp' →
      (∀ x ∈ lowerEarlyTerminalContactRequirements hyp' a b, x ∈ lowerEarlyTerminalTerminalRequirements C) →
      lowerEarlyTerminalContact p a b := by
    intro hyp' a b hat hsub
    have h1 := hK _ (hsub (lowerEarlyTerminalCmp hyp' a b) (by simp [lowerEarlyTerminalContactRequirements])) hat
    have h2 := hK _ (hsub (lowerEarlyTerminalCmp hyp' b a) (by simp [lowerEarlyTerminalContactRequirements])) hat
    exact hcontact a b h1 h2
  -- the D40 / D46 decisions
  have hD40 : lowerEarlyTerminalAt p [if lowerEarlyTerminalPrimary p then lowerEarlyTerminalD40 else
      lowerHistoryComplement lowerEarlyTerminalD40] := by
    unfold lowerEarlyTerminalPrimary
    by_cases h40 : lowerA p 40
    · rw [decide_eq_true h40]
      simp only [↓reduceIte]
      exact ((hp p).2.2.2.2.2.1).2 h40
    · rw [decide_eq_false h40]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact at_compl p _ (fun hD => h40 (((hp p).2.2.2.2.2.1).1 hD))
  have hat40 : lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C 2 ++ [if lowerEarlyTerminalPrimary p then
      lowerEarlyTerminalD40 else lowerHistoryComplement lowerEarlyTerminalD40]) := by
    intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact ha b hb
    · exact hD40 b hb
  have hD46 : ∀ yes : Bool, yes = decide (lowerA p 46) →
      lowerEarlyTerminalAt p [if yes then lowerEarlyTerminalD46 else lowerHistoryComplement lowerEarlyTerminalD46] := by
    intro yes hyes
    subst hyes
    by_cases h46 : lowerA p 46
    · rw [decide_eq_true h46]
      simp only [↓reduceIte]
      exact ((hp p).2.2.2.2.2.2).2 h46
    · rw [decide_eq_false h46]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact at_compl p _ (fun hD => h46 (((hp p).2.2.2.2.2.2).1 hD))
  have hat46 : ∀ yes : Bool, yes = decide (lowerA p 46) →
      lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C 2 ++ [if yes then lowerEarlyTerminalD46 else
        lowerHistoryComplement lowerEarlyTerminalD46]) := by
    intro yes hyes b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact ha b hb
    · exact hD46 yes hyes b hb
  refine ⟨hl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the eleven common contacts
    intro ab hab
    obtain ⟨a, b⟩ := ab
    refine hC (lowerEarlyTerminalHyp C 2) a b ha ?_
    intro x hx
    simp only [lowerEarlyTerminalTerminalRequirements, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatMap.2 ⟨(a,b), hab, hx⟩))))))
  · -- (312,311) -- middle
    refine hC _ ([3,1,2],[3,1,1]) (lowerEarlyTerminalMiddle (lowerEarlyTerminalPrimary p)) hat40 ?_
    intro x hx
    simp only [lowerEarlyTerminalTerminalRequirements, List.mem_append]
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))
    refine List.mem_flatMap.2 ⟨lowerEarlyTerminalPrimary p, ?_, ?_⟩
    · cases hb : lowerEarlyTerminalPrimary p <;> simp
    · simp only [List.mem_append]
      exact Or.inl (Or.inr hx)
  · -- middle -- (212,311)
    refine hC _ (lowerEarlyTerminalMiddle (lowerEarlyTerminalPrimary p)) ([2,1,2],[3,1,1]) hat40 ?_
    intro x hx
    simp only [lowerEarlyTerminalTerminalRequirements, List.mem_append]
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))
    refine List.mem_flatMap.2 ⟨lowerEarlyTerminalPrimary p, ?_, ?_⟩
    · cases hb : lowerEarlyTerminalPrimary p <;> simp
    · simp only [List.mem_append]
      exact Or.inr hx
  · -- the A46 alternative
    have hmemD : ∀ yes : Bool, ∀ x ∈ lowerEarlyTerminalContactRequirements
        (lowerEarlyTerminalHyp C 2 ++ [if yes then lowerEarlyTerminalD46 else lowerHistoryComplement lowerEarlyTerminalD46])
        ([1,1,1,2],[3,1,1]) (if yes then ([2,1,1,2],[3,1,1]) else ([1,1,1,2],[3,2])),
        x ∈ lowerEarlyTerminalTerminalRequirements C := by
      intro yes x hx
      simp only [lowerEarlyTerminalTerminalRequirements, List.mem_append]
      refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
      refine List.mem_flatMap.2 ⟨yes, ?_, hx⟩
      cases yes <;> simp
    by_cases h46 : lowerA p 46
    · left
      have := hC _ ([1,1,1,2],[3,1,1]) ([2,1,1,2],[3,1,1]) (hat46 true (by rw [decide_eq_true h46])) (hmemD true)
      exact this
    · right
      have := hC _ ([1,1,1,2],[3,1,1]) ([1,1,1,2],[3,2]) (hat46 false (by rw [decide_eq_false h46])) (hmemD false)
      exact this
  · -- last -- ([2],[2])
    refine hC (lowerEarlyTerminalHyp C 2) lowerEarlyTerminalLast ([2],[2]) ha ?_
    intro x hx
    simp only [lowerEarlyTerminalTerminalRequirements, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hx))
  · -- the final union join
    have hlast : lowerEarlyTerminalContact p lowerEarlyTerminalLast ([2],[2]) := by
      refine hC (lowerEarlyTerminalHyp C 2) lowerEarlyTerminalLast ([2],[2]) ha ?_
      intro x hx
      simp only [lowerEarlyTerminalTerminalRequirements, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hx))
    have hrev := hK (lowerEarlyTerminalCmp (lowerEarlyTerminalHyp C 2) ([2],[2]) ([2,1,1,2],[3,3])) (by
      simp only [lowerEarlyTerminalTerminalRequirements, List.mem_append]
      exact Or.inl (Or.inr (List.mem_singleton_self _))) ha
    have hun := hK (lowerEarlyTerminalHyp C 2, .unionCase 0) (by
      simp only [lowerEarlyTerminalTerminalRequirements, List.mem_append]
      exact Or.inr (List.mem_map.2 ⟨0, List.mem_range.2 (unionCases_pos C), rfl⟩)) ha
    exact hu ([2,1,1,2],[3,3]) lowerEarlyTerminalLast ([2],[2]) hlast hun hrev
