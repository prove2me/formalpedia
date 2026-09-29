-- Prove2me | solution 1 for Freiman.lower_guard_case_birth313
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T19:22:27.291077+00:00
-- url     : https://prove2.me/submissions/15a77d39-29d5-4095-b89f-7bbd44929659

import Definitions.Def_Freiman_lowerWordGuardData
import Mathlib.Tactic.IntervalCases

open Freiman

namespace M7Guard

/-- Decomposition of an infix of an append. -/
lemma infix_append_cases {α : Type*} {l a b : List α} (h : l <:+: a ++ b) :
    l <:+: a ∨ l <:+: b ∨
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁ ≠ [] ∧ l₂ ≠ [] ∧ l₁ <:+ a ∧ l₂ <+: b := by
  obtain ⟨s, t, hst⟩ := h
  rw [List.append_assoc, List.append_eq_append_iff] at hst
  rcases hst with ⟨a', ha, hb⟩ | ⟨c', _, hb⟩
  · rw [List.append_eq_append_iff] at hb
    rcases hb with ⟨x, hx, _⟩ | ⟨y, hl, hb'⟩
    · left; exact ⟨s, x, by rw [ha, hx, List.append_assoc]⟩
    · rcases a' with _ | ⟨d, a'⟩
      · right; left; exact ⟨[], t, by simp [hl, hb']⟩
      rcases y with _ | ⟨e, y⟩
      · left; exact ⟨s, [], by simp [ha, hl]⟩
      · right; right
        exact ⟨d :: a', e :: y, hl, by simp, by simp, ⟨s, ha.symm⟩, ⟨t, hb'.symm⟩⟩
  · right; left; exact ⟨c', t, by rw [hb, List.append_assoc]⟩

lemma infix_of_suffix_prefix {α : Type*} {l₁ l₂ a b : List α} (h₁ : l₁ <:+ a) (h₂ : l₂ <+: b) :
    l₁ ++ l₂ <:+: a ++ b := by
  obtain ⟨a', rfl⟩ := h₁
  obtain ⟨b', rfl⟩ := h₂
  exact ⟨a', b', by simp⟩

/-- The nontrivial splittings of the forbidden block. -/
lemma split_block {l₁ l₂ : List ℕ+} (h : l₁ ++ l₂ = [3,1,3,1,3]) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    (l₁ = [3] ∧ l₂ = [1,3,1,3]) ∨ (l₁ = [3,1] ∧ l₂ = [3,1,3]) ∨
    (l₁ = [3,1,3] ∧ l₂ = [1,3]) ∨ (l₁ = [3,1,3,1] ∧ l₂ = [3]) := by
  rcases l₁ with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l₁⟩⟩⟩⟩⟩
  · exact absurd rfl h₁
  · simp at h; obtain ⟨rfl, rfl⟩ := h; simp
  · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; simp
  · simp at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; simp
  · simp at h; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h; simp
  · simp at h; exact absurd h.2.2.2.2.2.2 h₂

lemma guardSuffix_iff (w u : List ℕ+) : lowerGuardSuffix w u = true ↔ u <:+ w := by
  unfold lowerGuardSuffix
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨_, h⟩
    rw [List.suffix_iff_eq_drop]; exact h.symm
  · intro h
    exact ⟨h.length_le, (List.suffix_iff_eq_drop.mp h).symm⟩

lemma guardSafe_not_infix {v : List ℕ+} (h : lowerGuardSafe v = true) :
    ¬ ([3,1,3,1,3] : List ℕ+) <:+: v := by
  rintro ⟨s, t, hst⟩
  unfold lowerGuardSafe at h
  simp only [Bool.not_eq_true', List.any_eq_false, List.mem_range, decide_eq_true_eq] at h
  apply h s.length
  · have := congrArg List.length hst; simp at this; omega
  · rw [← hst, List.append_assoc, List.drop_left]; rfl

lemma state_suffix (w : List ℕ+) : lowerGuardState w <:+ w := by
  unfold lowerGuardState
  split_ifs with h1 h2 h3 h4
  · exact (guardSuffix_iff _ _).mp h1
  · exact (guardSuffix_iff _ _).mp h2
  · exact (guardSuffix_iff _ _).mp h3
  · exact (guardSuffix_iff _ _).mp h4
  · exact List.drop_suffix _ _

/-- proper prefixes of the block that are suffixes of `w` are suffixes of the state -/
lemma suffix_state_3 {w : List ℕ+} (h : ([3] : List ℕ+) <:+ w) : ([3] : List ℕ+) <:+ lowerGuardState w := by
  unfold lowerGuardState
  split_ifs with h1 h2 h3 h4
  · rw [guardSuffix_iff] at h1
    rcases List.suffix_or_suffix_of_suffix h h1 with h' | h' <;> exact absurd h' (by decide)
  · decide
  · rw [guardSuffix_iff] at h3
    rcases List.suffix_or_suffix_of_suffix h h3 with h' | h' <;> exact absurd h' (by decide)
  · decide
  · rw [← guardSuffix_iff] at h; exact absurd h h4

lemma suffix_state_31 {w : List ℕ+} (h : ([3,1] : List ℕ+) <:+ w) : ([3,1] : List ℕ+) <:+ lowerGuardState w := by
  unfold lowerGuardState
  split_ifs with h1 h2 h3 h4
  · decide
  · rw [guardSuffix_iff] at h2
    rcases List.suffix_or_suffix_of_suffix h h2 with h' | h' <;> exact absurd h' (by decide)
  · decide
  · rw [← guardSuffix_iff] at h; exact absurd h h3
  · rw [← guardSuffix_iff] at h; exact absurd h h3

lemma suffix_state_313 {w : List ℕ+} (h : ([3,1,3] : List ℕ+) <:+ w) : ([3,1,3] : List ℕ+) <:+ lowerGuardState w := by
  unfold lowerGuardState
  split_ifs with h1 h2 h3 h4
  · rw [guardSuffix_iff] at h1
    rcases List.suffix_or_suffix_of_suffix h h1 with h' | h' <;> exact absurd h' (by decide)
  · decide
  all_goals (rw [← guardSuffix_iff] at h; exact absurd h h2)

lemma suffix_state_3131 {w : List ℕ+} (h : ([3,1,3,1] : List ℕ+) <:+ w) : ([3,1,3,1] : List ℕ+) <:+ lowerGuardState w := by
  unfold lowerGuardState
  split_ifs with h1 h2 h3 h4
  · decide
  all_goals (rw [← guardSuffix_iff] at h; exact absurd h h1)

/-- The boundary law, without the (unneeded) hypothesis `s ∈ lowerGuardStates`. -/
lemma boundary (w u : List ℕ+) (hw : ¬ ([3,1,3,1,3] : List ℕ+).IsInfix w)
    (hsafe : lowerGuardSafe (lowerGuardState w ++ u) = true) :
    ¬ ([3,1,3,1,3] : List ℕ+).IsInfix (w ++ u) := by
  intro hinf
  have hsafe' := guardSafe_not_infix hsafe
  rcases infix_append_cases hinf with h | h | ⟨l₁, l₂, heq, hn1, hn2, hsuf, hpre⟩
  · exact hw h
  · exact hsafe' (h.trans (List.suffix_append _ _).isInfix)
  · apply hsafe'
    rw [heq]
    apply infix_of_suffix_prefix _ hpre
    rcases split_block heq.symm hn1 hn2 with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact suffix_state_3 hsuf
    · exact suffix_state_31 hsuf
    · exact suffix_state_313 hsuf
    · exact suffix_state_3131 hsuf


lemma normalize_cases (p : LowerPair) : lowerNormalize p = p ∨ lowerNormalize p = (p.2, p.1) := by
  unfold lowerNormalize
  split_ifs <;> simp

lemma normalize_size (p : LowerPair) :
    (lowerNormalize p).1.length + (lowerNormalize p).2.length = p.1.length + p.2.length := by
  rcases normalize_cases p with h | h <;> rw [h] <;> simp [add_comm]

lemma lowerChild_eq (p : LowerPair) (l : LowerLabel) :
    lowerChild p l = ((lowerNormalize p).1 ++ l.1.reverse, (lowerNormalize p).2 ++ l.2) := rfl

lemma block_reverse : ([3,1,3,1,3] : List ℕ+).reverse = [3,1,3,1,3] := rfl

lemma not_infix_of_admissible {p : LowerPair} (hp : lowerAdmissible p) :
    ¬ ([3,1,3,1,3] : List ℕ+) <:+: (lowerNormalize p).1 ∧
    ¬ ([3,1,3,1,3] : List ℕ+) <:+: (lowerNormalize p).2 := by
  have h2 := hp.2
  have hA : ¬ ([3,1,3,1,3] : List ℕ+) <:+: p.1 := by
    intro h
    apply h2
    have h' : ([3,1,3,1,3] : List ℕ+).reverse <:+: p.1.reverse := List.reverse_infix.mpr h
    rw [block_reverse] at h'
    exact (h'.trans (List.prefix_append _ _).isInfix).trans (List.prefix_append _ _).isInfix
  have hB : ¬ ([3,1,3,1,3] : List ℕ+) <:+: p.2 := fun h =>
    h2 (h.trans (List.suffix_append _ _).isInfix)
  rcases normalize_cases p with h | h <;> rw [h] <;> exact ⟨by assumption, by assumption⟩

/-- an infix avoiding the letter 4 of `a ++ [4] ++ b` lies in `a` or in `b` -/
lemma split4 {x a b : List ℕ+} (h4 : (4 : ℕ+) ∉ x) (h : x <:+: a ++ [4] ++ b) :
    x <:+: a ∨ x <:+: b := by
  rw [List.append_assoc] at h
  rcases infix_append_cases h with h | h | ⟨l₁, l₂, heq, _, hn2, _, hpre⟩
  · exact Or.inl h
  · rw [List.singleton_append, List.infix_cons_iff] at h
    rcases h with h | h
    · rcases x with _ | ⟨c, x⟩
      · exact Or.inr List.nil_infix
      · exfalso; apply h4
        rw [List.cons_prefix_cons] at h
        rw [h.1]; exact List.mem_cons_self
    · exact Or.inr h
  · exfalso
    rcases l₂ with _ | ⟨e, l₂⟩
    · exact hn2 rfl
    · rw [List.singleton_append, List.cons_prefix_cons] at hpre
      apply h4
      rw [heq, hpre.1]
      simp

lemma birth_core (w e s : List ℕ+) (hs : lowerGuardState w = s) (he : e ≠ [])
    (hnew : ([3,1,3] : List ℕ+) <:+ w ++ e)
    (hc2 : lowerGuardState (s ++ e) = [3,1,3,1] → e ≠ [] → s = [3,1,3] ∧ e = [1]) :
    lowerGuardState (s ++ e) = [3,1,3] := by
  have hs3 : ([3] : List ℕ+) <:+ w → ([3] : List ℕ+) <:+ s := fun h => hs ▸ suffix_state_3 h
  have hs31 : ([3,1] : List ℕ+) <:+ w → ([3,1] : List ℕ+) <:+ s := fun h => hs ▸ suffix_state_31 h
  -- the block 313 is a suffix of s ++ e
  have k313 : ([3,1,3] : List ℕ+) <:+ s ++ e := by
    obtain ⟨t, ht⟩ := hnew
    rw [List.append_eq_append_iff] at ht
    rcases ht with ⟨a', hw, h313⟩ | ⟨c', _, he'⟩
    · have ha' : a' <:+ w := ⟨t, hw.symm⟩
      rcases a' with _ | ⟨x, _ | ⟨y, _ | ⟨z, a'⟩⟩⟩
      · simp at h313; rw [← h313]; exact List.suffix_append _ _
      · simp at h313; obtain ⟨rfl, rfl⟩ := h313
        obtain ⟨r, hr⟩ := hs3 ha'
        exact ⟨r, by rw [← hr]; simp⟩
      · simp at h313; obtain ⟨rfl, rfl, rfl⟩ := h313
        obtain ⟨r, hr⟩ := hs31 ha'
        exact ⟨r, by rw [← hr]; simp⟩
      · simp at h313
        exact absurd h313.2.2.2.2 he
    · rw [he']; exact ⟨s ++ c', by simp⟩
  -- the block 3131 is not a suffix of s ++ e
  have k3131 : ¬ ([3,1,3,1] : List ℕ+) <:+ s ++ e := by
    intro h1
    have h1' : lowerGuardState (s ++ e) = [3,1,3,1] := by
      unfold lowerGuardState; rw [if_pos ((guardSuffix_iff _ _).mpr h1)]
    obtain ⟨_, he1⟩ := hc2 h1' he
    rw [he1] at hnew
    obtain ⟨t, ht⟩ := hnew
    have := (List.append_inj' (show (t ++ [3,1]) ++ [3] = w ++ [1] by simpa using ht) rfl).2
    exact absurd this (by decide)
  unfold lowerGuardState
  split_ifs with h1 h2
  · exact absurd ((guardSuffix_iff _ _).mp h1) k3131
  · rfl
  all_goals exact absurd ((guardSuffix_iff _ _).mpr k313) h2

end M7Guard

open M7Guard in
theorem solution (p : LowerPair) (c : LowerGuardCase) (hv : lowerGuardCaseValid c) (hf : lowerGuardFits c p)
    (l : LowerLabel) (hl : l ∈ c.labels) (right : Bool)
    (hnew : lowerEnds (lowerSide (lowerChild p l) right) [3,1,3])
    (hchanged : lowerSide (lowerChild p l) right ≠ lowerSide (lowerNormalize p) right) : l = ([2],[3]) := by
  have hc := (hv.2.2.1 l hl).2.2.2.2 right
  dsimp only at hc
  unfold lowerEnds at hnew
  rw [hf.1] at hc
  cases right
  · -- left side
    change ([3,1,3] : List ℕ+) <:+ (lowerNormalize p).1 ++ l.1.reverse at hnew
    change (lowerNormalize p).1 ++ l.1.reverse ≠ (lowerNormalize p).1 at hchanged
    change (lowerGuardState ((lowerGuardState (lowerNormalize p).1) ++ l.1.reverse) = [3,1,3] → l.1.reverse ≠ [] → _) ∧
      (lowerGuardState ((lowerGuardState (lowerNormalize p).1) ++ l.1.reverse) = [3,1,3,1] → l.1.reverse ≠ [] →
        lowerGuardState (lowerNormalize p).1 = [3,1,3] ∧ l.1.reverse = [1]) ∧ _ at hc
    have he : l.1.reverse ≠ [] := fun h => hchanged (by rw [h, List.append_nil])
    exact (hc.1 (birth_core _ _ _ rfl he hnew hc.2.1) he).2.1
  · -- right side
    change ([3,1,3] : List ℕ+) <:+ (lowerNormalize p).2 ++ l.2 at hnew
    change (lowerNormalize p).2 ++ l.2 ≠ (lowerNormalize p).2 at hchanged
    change (lowerGuardState ((lowerGuardState (lowerNormalize p).2) ++ l.2) = [3,1,3] → l.2 ≠ [] → _) ∧
      (lowerGuardState ((lowerGuardState (lowerNormalize p).2) ++ l.2) = [3,1,3,1] → l.2 ≠ [] →
        lowerGuardState (lowerNormalize p).2 = [3,1,3] ∧ l.2 = [1]) ∧ _ at hc
    have he : l.2 ≠ [] := fun h => hchanged (by rw [h, List.append_nil])
    exact (hc.1 (birth_core _ _ _ rfl he hnew hc.2.1) he).2.1
