-- Prove2me | solution 1 for FriedbergMuchnik.priority_eventually_quiescent
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T21:55:21.441827+00:00
-- url     : https://prove2.me/submissions/d77df086-b995-44bd-9008-efbeb15f62da

import Definitions.Def_FriedbergMuchnik_Priority

set_option autoImplicit false

open FriedbergMuchnik

private def selected (s : ℕ) : Option ℕ :=
  (List.range s).find? (wantsAttention s (priorityStage s))

private def entry (s q : ℕ) : ℕ × Bool :=
  (priorityStage s).2[q]?.getD (0, false)

private theorem entries_length (s : ℕ) : (priorityStage s).2.length = s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      simp only [priorityStage, priorityStep]
      split <;> simp [ih]

private theorem entry_next (s q : ℕ) (hq : q < s) :
    entry (s + 1) q =
      match selected s with
      | none => entry s q
      | some p => if p < q then (Nat.pair q (s + 1), false)
          else if q = p then ((entry s q).1, true) else entry s q := by
  have hb : q < (priorityStage s).2.length := by simpa [entries_length] using hq
  cases hs : selected s with
  | none =>
      change (List.range s).find? (wantsAttention s (priorityStage s)) = none at hs
      simp only [entry, priorityStage, priorityStep, hs, List.getElem?_append_left hb]
  | some p =>
      have hm : q < ((priorityStage s).2.mapIdx fun k e =>
          if p < k then (Nat.pair k (s + 1), false)
          else if k = p then (e.1, true) else e).length := by simpa using hb
      change (List.range s).find? (wantsAttention s (priorityStage s)) = some p at hs
      simp only [entry, priorityStage, priorityStep, hs]
      rw [List.getElem?_append_left hm, List.getElem?_mapIdx,
        List.getElem?_eq_getElem hb]
      simp only [Option.map_some, Option.getD_some]

private theorem selected_info {s p : ℕ} (h : selected s = some p) :
    p < s ∧ wantsAttention s (priorityStage s) p = true ∧
      (entry s p).2 = false := by
  have hm := List.mem_of_find?_eq_some h
  have ht := List.find?_some h
  refine ⟨by simpa using hm, ht, ?_⟩
  have ht' := ht
  change ((! (entry s p).2) && _) = true at ht'
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht'
  exact ht'.1

private theorem selected_le {s q : ℕ} (hq : q < s)
    (ha : wantsAttention s (priorityStage s) q = true) :
    ∃ p, p ≤ q ∧ selected s = some p := by
  cases hs : selected s with
  | none =>
      have hn := List.find?_eq_none.mp hs q (by simpa using hq)
      exact False.elim (hn ha)
  | some p =>
      refine ⟨p, ?_, rfl⟩
      obtain ⟨_, j, hj, hjp, hbefore⟩ := List.find?_eq_some_iff_getElem.mp hs
      simp only [List.getElem_range] at hjp
      subst j
      by_contra h
      have hb := hbefore q (by omega)
      simp only [List.getElem_range, ha, Bool.not_true, Bool.false_eq_true] at hb

private theorem true_persists {q a : ℕ} (hqa : q < a)
    (ha : (entry a q).2 = true)
    (hhigh : ∀ s, a ≤ s → ∀ p, p < q → selected s ≠ some p) :
    ∀ s, a ≤ s → (entry s q).2 = true := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact ha
  | succ s hs ih =>
      rw [entry_next s q (by omega)]
      cases hp : selected s with
      | none => exact ih
      | some p =>
          have hnot : ¬p < q := fun h => hhigh s hs p h hp
          simp only [hnot, ↓reduceIte]
          split
          · rfl
          · exact ih

private theorem eventually_no_selection (q : ℕ) :
    ∃ a, q < a ∧ ∀ s, a ≤ s → ∀ p, p ≤ q → selected s ≠ some p := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      have hprev : ∃ a, q < a ∧
          ∀ s, a ≤ s → ∀ p, p < q → selected s ≠ some p := by
        cases q with
        | zero => exact ⟨1, by omega, by intros; omega⟩
        | succ q =>
            obtain ⟨a, ha, hstop⟩ := ih q (by omega)
            exact ⟨a + 1, by omega, fun s hs p hp => hstop s (by omega) p (by omega)⟩
      obtain ⟨a, hqa, hhigh⟩ := hprev
      by_cases hact : ∃ s, a ≤ s ∧ selected s = some q
      · obtain ⟨s, hs, hsel⟩ := hact
        have htrue : (entry (s + 1) q).2 = true := by
          rw [entry_next s q (by omega), hsel]
          simp
        have hper := true_persists (q := q) (a := s + 1) (by omega) htrue
          (fun t ht p hp => hhigh t (by omega) p hp)
        refine ⟨s + 1, by omega, ?_⟩
        intro t ht p hp hsel'
        by_cases heq : p = q
        · subst p
          have hf := (selected_info hsel').2.2
          have ht' := hper t ht
          simp [ht'] at hf
        · exact hhigh t (by omega) p (by omega) hsel'
      · refine ⟨a, hqa, ?_⟩
        intro s hs p hp hsel
        by_cases heq : p = q
        · exact hact ⟨s, hs, heq ▸ hsel⟩
        · exact hhigh s hs p (by omega) hsel

/-- Every requirement eventually has a fixed entry, and no requirement of
higher or equal priority requests attention from that point onward. -/
theorem solution (q : ℕ) :
    ∃ a : ℕ, q < a ∧ ∀ s : ℕ, a ≤ s →
      (priorityStage s).2[q]?.getD (0, false) =
        (priorityStage a).2[q]?.getD (0, false) ∧
      ∀ p : ℕ, p ≤ q → wantsAttention s (priorityStage s) p = false := by
  obtain ⟨a, hqa, hstop⟩ := eventually_no_selection q
  refine ⟨a, hqa, ?_⟩
  have hstable : ∀ s, a ≤ s → entry s q = entry a q := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => rfl
    | succ s hs ih =>
        rw [entry_next s q (by omega)]
        cases hp : selected s with
        | none => exact ih
        | some p =>
            have hlt : q < p := by
              by_contra h
              exact hstop s hs p (by omega) hp
            simpa [show ¬p < q by omega, show q ≠ p by omega] using ih
  intro s hs
  refine ⟨hstable s hs, ?_⟩
  intro p hp
  cases ha : wantsAttention s (priorityStage s) p with
  | false => rfl
  | true =>
      obtain ⟨r, hr, hsel⟩ := selected_le (by omega : p < s) ha
      exact False.elim (hstop s hs r (by omega) hsel)
