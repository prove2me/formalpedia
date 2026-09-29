-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_short_contacts
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:42:04.496685+00:00
-- url     : https://prove2.me/submissions/53457253-b406-48bf-8a7d-ad8b93f6f981

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

lemma chain_of_pairs {α : Type} (R : α → α → Prop) : ∀ ls : List α,
    (∀ a b, (a,b) ∈ ls.zip ls.tail → R a b) → ls.IsChain R
  | [], _ => by simp
  | [a], _ => by simp
  | a :: b :: rest, h => by
      refine List.isChain_cons_cons.2 ⟨h a b (by simp), chain_of_pairs R (b :: rest) ?_⟩
      intro x y hxy
      apply h x y
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hxy ⊢
      exact Or.inr hxy

theorem solution (C : LowerEarlyTerminalCatalog) (p : LowerPair) (mode : ℕ) (hm : mode<2)
    (h : lowerEarlyTerminalRequiredSound C p mode) (ha : lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C mode))
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true)
    (hcontact : ∀ a b, lowerEarlyTerminalKindHolds p (.compare (section14LabelWords a) true (section14LabelWords b) false false) →
      lowerEarlyTerminalKindHolds p (.compare (section14LabelWords b) true (section14LabelWords a) false false) →
      lowerEarlyTerminalContact p a b) :
    (if mode=0 then lowerEarlyTerminalFirst else lowerEarlyTerminalSecond).IsChain (lowerEarlyTerminalContact p) := by
  apply chain_of_pairs
  intro a b hab
  have key : ∀ x ∈ lowerEarlyTerminalContactRequirements (lowerEarlyTerminalHyp C mode) a b,
      x ∈ lowerEarlyTerminalRequirements C mode := by
    intro x hx
    unfold lowerEarlyTerminalRequirements
    rw [if_pos hm]
    simp only [lowerEarlyTerminalShortRequirements]
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨(a,b), hab, hx⟩)
  have h1 := h _ (key (lowerEarlyTerminalCmp (lowerEarlyTerminalHyp C mode) a b)
    (by simp [lowerEarlyTerminalContactRequirements])) ha
  have h2 := h _ (key (lowerEarlyTerminalCmp (lowerEarlyTerminalHyp C mode) b a)
    (by simp [lowerEarlyTerminalContactRequirements])) ha
  exact hcontact a b h1 h2
