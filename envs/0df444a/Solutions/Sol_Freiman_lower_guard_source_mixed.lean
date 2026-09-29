-- Prove2me | solution 1 for Freiman.lower_guard_source_mixed
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T19:29:51.148729+00:00
-- url     : https://prove2.me/submissions/dda3e4fd-4c83-455a-822a-5c473c043326

import Definitions.Def_Freiman_lowerWordGuardData
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs

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


/-! ### catalogue access -/

def rowCase (r : LowerGuardPrinted) (ctx : LowerPair) : LowerGuardCase :=
  ⟨r.mixed, ctx, r.branch, r.labels, r.reason, r.run⟩

instance : Inhabited LowerGuardPrinted := ⟨⟨0, [], false, "", [], "", false⟩⟩

def row (j : ℕ) : LowerGuardPrinted := lowerGuardPrintedRows.getD (j-1) default

/-! ### guard states of admissible pairs -/

lemma cores_ok : ∀ c ∈ lowerCores, c.1 ≠ [] ∧ c.2 ≠ [] ∧
    (∀ d ∈ c.1.drop (c.1.length - 1), (d:ℕ) ≤ 3) ∧ (∀ d ∈ c.2.drop (c.2.length - 1), (d:ℕ) ≤ 3) := by
  decide

lemma drop_last_append {c u : List ℕ+} (hc : ∀ d ∈ c.drop (c.length - 1), (d:ℕ) ≤ 3)
    (hu : ∀ d ∈ u, (d:ℕ) ≤ 3) :
    ∀ d ∈ (c ++ u).drop ((c ++ u).length - 1), (d:ℕ) ≤ 3 := by
  rcases u with _ | ⟨a, u⟩
  · simpa using hc
  · intro d hd
    rw [List.drop_append, List.drop_eq_nil_of_le (by simp)] at hd
    simp only [List.nil_append] at hd
    exact hu d ((List.drop_sublist _ _).subset hd)

lemma state_mem_of {w : List ℕ+} (hne : w ≠ [])
    (hlast : ∀ d ∈ w.drop (w.length - 1), (d:ℕ) ≤ 3) :
    lowerGuardState w ∈ lowerGuardStates := by
  unfold lowerGuardState
  split_ifs
  · decide
  · decide
  · decide
  · decide
  · have hlen : (w.drop (w.length - 1)).length = 1 := by
      rw [List.length_drop]; have := List.length_pos_of_ne_nil hne; omega
    obtain ⟨d, hd⟩ := List.length_eq_one_iff.mp hlen
    rw [hd]
    have h3 := hlast d (by rw [hd]; exact List.mem_singleton_self d)
    have hpos := d.pos
    have : (d:ℕ) = 1 ∨ (d:ℕ) = 2 ∨ (d:ℕ) = 3 := by omega
    rcases this with h | h | h
    · rw [PNat.eq (h.trans rfl : (d:ℕ) = ((1:ℕ+):ℕ))]; decide
    · rw [PNat.eq (h.trans rfl : (d:ℕ) = ((2:ℕ+):ℕ))]; decide
    · rw [PNat.eq (h.trans rfl : (d:ℕ) = ((3:ℕ+):ℕ))]; decide

lemma states_of_admissible {p : LowerPair} (hp : lowerAdmissible p) :
    lowerGuardState (lowerNormalize p).1 ∈ lowerGuardStates ∧
    lowerGuardState (lowerNormalize p).2 ∈ lowerGuardStates := by
  obtain ⟨⟨c, hc, u, v, hpq, hu, hv⟩, _⟩ := hp
  obtain ⟨hc1, hc2, hl1, hl2⟩ := cores_ok c hc
  have h1 : lowerGuardState p.1 ∈ lowerGuardStates := by
    rw [hpq]; exact state_mem_of (by simp [hc1]) (drop_last_append hl1 hu)
  have h2 : lowerGuardState p.2 ∈ lowerGuardStates := by
    rw [hpq]; exact state_mem_of (by simp [hc2]) (drop_last_append hl2 hv)
  rcases normalize_cases p with h | h <;> rw [h]
  · exact ⟨h1, h2⟩
  · exact ⟨h2, h1⟩

lemma s3_iff (w : List ℕ+) : ([3] : List ℕ+) <:+ w ↔ ([3] : List ℕ+) <:+ lowerGuardState w :=
  ⟨suffix_state_3, fun h => h.trans (state_suffix w)⟩
lemma s31_iff (w : List ℕ+) : ([3,1] : List ℕ+) <:+ w ↔ ([3,1] : List ℕ+) <:+ lowerGuardState w :=
  ⟨suffix_state_31, fun h => h.trans (state_suffix w)⟩
lemma s3131_iff (w : List ℕ+) : ([3,1,3,1] : List ℕ+) <:+ w ↔ ([3,1,3,1] : List ℕ+) <:+ lowerGuardState w :=
  ⟨suffix_state_3131, fun h => h.trans (state_suffix w)⟩


set_option maxRecDepth 10000 in
theorem memM : ∀ r ∈ lowerGuardPrintedRows.drop 17, ∀ ctx ∈ r.contexts,
    rowCase r ctx ∈ lowerGuardCases := by
  decide +kernel

lemma use_row {p : LowerPair} {s1 s2 : List ℕ+} {l : LowerLabel} (j : ℕ)
    (hj : row j ∈ lowerGuardPrintedRows.drop 17)
    (hctx : (s1, s2) ∈ (row j).contexts) (hm : (row j).mixed = true ↔ lowerMixed p)
    (hb : lowerGuardBranch (row j).branch p) (hl : l ∈ (row j).labels) :
    ∃ c ∈ lowerGuardCases, (c.before = (s1, s2) ∧ (c.mixed = true ↔ lowerMixed p) ∧
      lowerGuardBranch c.branch p) ∧ l ∈ c.labels :=
  ⟨rowCase (row j) (s1, s2), memM _ hj _ hctx, ⟨rfl, hm, hb⟩, hl⟩

lemma ctx18 : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates, True → (s1, s2) ∈ (row 18).contexts := by decide
lemma ctx19 : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates, ¬ ([3,1] : List ℕ+) <:+ s1 → (s1, s2) ∈ (row 19).contexts := by decide
lemma ctx20 : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates, ¬ ([3,1] : List ℕ+) <:+ s1 → (s1, s2) ∈ (row 20).contexts := by decide
lemma ctx21 : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates, ¬ ([3,1] : List ℕ+) <:+ s1 → (s1, s2) ∈ (row 21).contexts := by decide
lemma ctx22 : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates, ¬ ([3,1] : List ℕ+) <:+ s1 ∧ ¬ ([3,1,3,1] : List ℕ+) <:+ s2 → (s1, s2) ∈ (row 22).contexts := by decide
lemma ctx23 : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates, ¬ ([3,1] : List ℕ+) <:+ s1 ∧ ¬ ([3,1,3,1] : List ℕ+) <:+ s2 → (s1, s2) ∈ (row 23).contexts := by decide
lemma ctx24 : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates, ¬ ([3,1] : List ℕ+) <:+ s1 ∧ ¬ ([3,1,3,1] : List ℕ+) <:+ s2 → (s1, s2) ∈ (row 24).contexts := by decide
lemma ctx25 : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates, ¬ ([3,1,3,1] : List ℕ+) <:+ s2 ∧ ¬ ([3] : List ℕ+) <:+ s2 → (s1, s2) ∈ (row 25).contexts := by decide
lemma ctx27 : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates, ([3,1] : List ℕ+) <:+ s1 → (s1, s2) ∈ (row 27).contexts := by decide
lemma ctx28 : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates, ([3,1] : List ℕ+) <:+ s1 ∧ ¬ ([3,1,3,1] : List ℕ+) <:+ s1 ∧ ¬ ([3,1,3,1] : List ℕ+) <:+ s2 → (s1, s2) ∈ (row 28).contexts := by decide
lemma ctx29 : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates, ([3,1] : List ℕ+) <:+ s1 ∧ ¬ ([3,1,3,1] : List ℕ+) <:+ s1 ∧ ¬ ([3,1,3,1] : List ℕ+) <:+ s2 → (s1, s2) ∈ (row 29).contexts := by decide
lemma ctx30 : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates, ([3,1] : List ℕ+) <:+ s1 ∧ ¬ ([3,1,3,1] : List ℕ+) <:+ s1 ∧ ¬ ([3,1,3,1] : List ℕ+) <:+ s2 → (s1, s2) ∈ (row 30).contexts := by decide
lemma ctx31 : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates, ([3,1,3,1] : List ℕ+) <:+ s1 ∧ ¬ ([3,1,3,1] : List ℕ+) <:+ s2 → (s1, s2) ∈ (row 31).contexts := by decide
lemma ctx32 : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates, ([3,1,3,1] : List ℕ+) <:+ s1 ∧ ¬ ([3,1,3,1] : List ℕ+) <:+ s2 → (s1, s2) ∈ (row 32).contexts := by decide
lemma ctx33 : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates, ([3,1,3,1] : List ℕ+) <:+ s1 ∧ ¬ ([3,1,3,1] : List ℕ+) <:+ s2 → (s1, s2) ∈ (row 33).contexts := by decide
lemma br18 (p : LowerPair) : lowerGuardBranch (row 18).branch p ↔ (lowerMixed p ∧ lowerH p 2) := Iff.rfl
lemma br19 (p : LowerPair) : lowerGuardBranch (row 19).branch p ↔ ((lowerMixed p ∧ ¬ lowerH p 2 ∧ lowerH p 5) ∧ ¬ lowerL p ∧ lowerH p 6 ∧ lowerH p 7) := Iff.rfl
lemma br20 (p : LowerPair) : lowerGuardBranch (row 20).branch p ↔ ((lowerMixed p ∧ ¬ lowerH p 2 ∧ lowerH p 5) ∧ ¬ lowerL p ∧ ¬ lowerH p 6) := Iff.rfl
lemma br21 (p : LowerPair) : lowerGuardBranch (row 21).branch p ↔ ((lowerMixed p ∧ ¬ lowerH p 2 ∧ lowerH p 5) ∧ ¬ lowerL p ∧ lowerH p 6 ∧ ¬ lowerH p 7) := Iff.rfl
lemma br22 (p : LowerPair) : lowerGuardBranch (row 22).branch p ↔ ((lowerMixed p ∧ ¬ lowerH p 2 ∧ ¬ lowerH p 5) ∧ ¬ lowerRStar p ∧ lowerH p 21 ∧ lowerH p 17) := Iff.rfl
lemma br23 (p : LowerPair) : lowerGuardBranch (row 23).branch p ↔ ((lowerMixed p ∧ ¬ lowerH p 2 ∧ ¬ lowerH p 5) ∧ ¬ lowerRStar p ∧ lowerH p 21 ∧ ¬ lowerH p 17) := Iff.rfl
lemma br24 (p : LowerPair) : lowerGuardBranch (row 24).branch p ↔ ((lowerMixed p ∧ ¬ lowerH p 2 ∧ ¬ lowerH p 5) ∧ ¬ lowerRStar p ∧ ¬ lowerH p 21 ∧ (lowerEnds (lowerNormalize p).2 [3] ∨ ¬ lowerH p 23)) := Iff.rfl
lemma br25 (p : LowerPair) : lowerGuardBranch (row 25).branch p ↔ ((lowerMixed p ∧ ¬ lowerH p 2 ∧ ¬ lowerH p 5) ∧ ¬ lowerRStar p ∧ ¬ lowerH p 21 ∧ ¬ lowerEnds (lowerNormalize p).2 [3] ∧ lowerH p 23) := Iff.rfl
lemma br27 (p : LowerPair) : lowerGuardBranch (row 27).branch p ↔ ((lowerMixed p ∧ ¬ lowerH p 2 ∧ lowerH p 5) ∧ lowerL p) := Iff.rfl
lemma br28 (p : LowerPair) : lowerGuardBranch (row 28).branch p ↔ ((lowerMixed p ∧ ¬ lowerH p 2 ∧ ¬ lowerH p 5) ∧ ¬ lowerRStar p ∧ lowerH p 21 ∧ lowerH p 17) := Iff.rfl
lemma br29 (p : LowerPair) : lowerGuardBranch (row 29).branch p ↔ ((lowerMixed p ∧ ¬ lowerH p 2 ∧ ¬ lowerH p 5) ∧ ¬ lowerRStar p ∧ lowerH p 21 ∧ ¬ lowerH p 17) := Iff.rfl
lemma br30 (p : LowerPair) : lowerGuardBranch (row 30).branch p ↔ ((lowerMixed p ∧ ¬ lowerH p 2 ∧ ¬ lowerH p 5) ∧ ¬ lowerRStar p ∧ ¬ lowerH p 21 ∧ (lowerEnds (lowerNormalize p).2 [3] ∨ ¬ lowerH p 23)) := Iff.rfl
lemma br31 (p : LowerPair) : lowerGuardBranch (row 31).branch p ↔ ((lowerMixed p ∧ ¬ lowerH p 2 ∧ ¬ lowerH p 5) ∧ ¬ lowerRStar p ∧ lowerH p 21 ∧ lowerH p 17) := Iff.rfl
lemma br32 (p : LowerPair) : lowerGuardBranch (row 32).branch p ↔ ((lowerMixed p ∧ ¬ lowerH p 2 ∧ ¬ lowerH p 5) ∧ ¬ lowerRStar p ∧ lowerH p 21 ∧ ¬ lowerH p 17) := Iff.rfl
lemma br33 (p : LowerPair) : lowerGuardBranch (row 33).branch p ↔ ((lowerMixed p ∧ ¬ lowerH p 2 ∧ ¬ lowerH p 5) ∧ ¬ lowerRStar p ∧ ¬ lowerH p 21 ∧ (lowerEnds (lowerNormalize p).2 [3] ∨ ¬ lowerH p 23)) := Iff.rfl

end M7Guard

open M7Guard in
theorem solution (p : LowerPair) (hp : lowerAdmissible p) (hpar : lowerMixed p)
    (l : LowerLabel) (hl : l ∈ lowerMixedList p) :
    ∃ c ∈ lowerGuardCases, lowerGuardFits c p ∧ l ∈ c.labels := by
  obtain ⟨hs1, hs2⟩ := states_of_admissible hp
  have hL : lowerL p ↔ ([3,1] : List ℕ+) <:+ lowerGuardState (lowerNormalize p).1 := s31_iff _
  have hLS : lowerLStar p ↔ ([3,1,3,1] : List ℕ+) <:+ lowerGuardState (lowerNormalize p).1 := s3131_iff _
  have hRS : lowerRStar p ↔ ([3,1,3,1] : List ℕ+) <:+ lowerGuardState (lowerNormalize p).2 := s3131_iff _
  have hE3 : lowerEnds (lowerNormalize p).2 [3] ↔ ([3] : List ℕ+) <:+ lowerGuardState (lowerNormalize p).2 := s3_iff _
  unfold lowerGuardFits
  set s1 := lowerGuardState (lowerNormalize p).1 with hs1def
  set s2 := lowerGuardState (lowerNormalize p).2 with hs2def
  have hmix : ∀ j, (row j).mixed = true → ((row j).mixed = true ↔ lowerMixed p) :=
    fun j h => iff_of_true h hpar
  unfold lowerMixedList at hl
  dsimp only at hl
  by_cases hH2 : lowerH p 2
  · rw [if_pos hH2] at hl
    exact use_row 18 (by decide) (ctx18 s1 hs1 s2 hs2 trivial) (hmix 18 rfl)
      ((br18 p).mpr ⟨hpar, hH2⟩) (by revert l hl; decide)
  · rw [if_neg hH2] at hl
    by_cases hH5 : lowerH p 5
    · rw [if_pos hH5] at hl
      by_cases hLp : lowerL p
      · rw [if_pos hLp] at hl
        exact use_row 27 (by decide) (ctx27 s1 hs1 s2 hs2 (hL.mp hLp)) (hmix 27 rfl)
          ((br27 p).mpr ⟨⟨hpar, hH2, hH5⟩, hLp⟩) (by revert l hl; decide)
      · rw [if_neg hLp] at hl
        have hL' := hL.not.mp hLp
        by_cases h67 : lowerH p 6 ∧ lowerH p 7
        · rw [if_pos h67] at hl
          exact use_row 19 (by decide) (ctx19 s1 hs1 s2 hs2 hL') (hmix 19 rfl)
            ((br19 p).mpr ⟨⟨hpar, hH2, hH5⟩, hLp, h67.1, h67.2⟩) (by revert l hl; decide)
        · rw [if_neg h67] at hl
          by_cases hH6 : lowerH p 6
          · exact use_row 21 (by decide) (ctx21 s1 hs1 s2 hs2 hL') (hmix 21 rfl)
              ((br21 p).mpr ⟨⟨hpar, hH2, hH5⟩, hLp, hH6, fun h7 => h67 ⟨hH6, h7⟩⟩) (by revert l hl; decide)
          · exact use_row 20 (by decide) (ctx20 s1 hs1 s2 hs2 hL') (hmix 20 rfl)
              ((br20 p).mpr ⟨⟨hpar, hH2, hH5⟩, hLp, hH6⟩) (by revert l hl; decide)
    · rw [if_neg hH5] at hl
      by_cases hRSp : lowerRStar p
      · rw [if_pos hRSp] at hl
        simp at hl
      · rw [if_neg hRSp] at hl
        have hRS' := hRS.not.mp hRSp
        by_cases h23 : ¬ lowerH p 21 ∧ ¬ lowerEnds (lowerNormalize p).2 [3] ∧ lowerH p 23
        · rw [if_pos h23] at hl
          exact use_row 25 (by decide) (ctx25 s1 hs1 s2 hs2 ⟨hRS', hE3.not.mp h23.2.1⟩) (hmix 25 rfl)
            ((br25 p).mpr ⟨⟨hpar, hH2, hH5⟩, hRSp, h23.1, h23.2.1, h23.2.2⟩) (by revert l hl; decide)
        · rw [if_neg h23] at hl
          have hchain : ¬ lowerH p 21 → (lowerEnds (lowerNormalize p).2 [3] ∨ ¬ lowerH p 23) := by
            intro h21
            by_cases hE : lowerEnds (lowerNormalize p).2 [3]
            · exact Or.inl hE
            · exact Or.inr (fun h => h23 ⟨h21, hE, h⟩)
          by_cases hLSp : lowerLStar p
          · rw [if_pos hLSp] at hl
            have hc := ctx31 s1 hs1 s2 hs2 ⟨hLS.mp hLSp, hRS'⟩
            have hc' := ctx32 s1 hs1 s2 hs2 ⟨hLS.mp hLSp, hRS'⟩
            have hc'' := ctx33 s1 hs1 s2 hs2 ⟨hLS.mp hLSp, hRS'⟩
            by_cases hH21 : lowerH p 21
            · by_cases hH17 : lowerH p 17
              · exact use_row 31 (by decide) hc (hmix 31 rfl)
                  ((br31 p).mpr ⟨⟨hpar, hH2, hH5⟩, hRSp, hH21, hH17⟩) (by revert l hl; decide)
              · exact use_row 32 (by decide) hc' (hmix 32 rfl)
                  ((br32 p).mpr ⟨⟨hpar, hH2, hH5⟩, hRSp, hH21, hH17⟩) (by revert l hl; decide)
            · exact use_row 33 (by decide) hc'' (hmix 33 rfl)
                ((br33 p).mpr ⟨⟨hpar, hH2, hH5⟩, hRSp, hH21, hchain hH21⟩) (by revert l hl; decide)
          · rw [if_neg hLSp] at hl
            have hLS' := hLS.not.mp hLSp
            by_cases hH21 : lowerH p 21
            · rw [if_pos hH21] at hl
              by_cases hLp : lowerL p
              · rw [if_pos hLp] at hl
                have hc := ctx28 s1 hs1 s2 hs2 ⟨hL.mp hLp, hLS', hRS'⟩
                have hc' := ctx29 s1 hs1 s2 hs2 ⟨hL.mp hLp, hLS', hRS'⟩
                by_cases hH17 : lowerH p 17
                · rw [if_pos hH17] at hl
                  exact use_row 28 (by decide) hc (hmix 28 rfl)
                    ((br28 p).mpr ⟨⟨hpar, hH2, hH5⟩, hRSp, hH21, hH17⟩) (by revert l hl; decide)
                · rw [if_neg hH17] at hl
                  exact use_row 29 (by decide) hc' (hmix 29 rfl)
                    ((br29 p).mpr ⟨⟨hpar, hH2, hH5⟩, hRSp, hH21, hH17⟩) (by revert l hl; decide)
              · rw [if_neg hLp] at hl
                have hc := ctx22 s1 hs1 s2 hs2 ⟨hL.not.mp hLp, hRS'⟩
                have hc' := ctx23 s1 hs1 s2 hs2 ⟨hL.not.mp hLp, hRS'⟩
                by_cases hH17 : lowerH p 17
                · rw [if_pos hH17] at hl
                  exact use_row 22 (by decide) hc (hmix 22 rfl)
                    ((br22 p).mpr ⟨⟨hpar, hH2, hH5⟩, hRSp, hH21, hH17⟩) (by revert l hl; decide)
                · rw [if_neg hH17] at hl
                  exact use_row 23 (by decide) hc' (hmix 23 rfl)
                    ((br23 p).mpr ⟨⟨hpar, hH2, hH5⟩, hRSp, hH21, hH17⟩) (by revert l hl; decide)
            · rw [if_neg hH21] at hl
              by_cases hLp : lowerL p
              · rw [if_pos hLp] at hl
                exact use_row 30 (by decide) (ctx30 s1 hs1 s2 hs2 ⟨hL.mp hLp, hLS', hRS'⟩) (hmix 30 rfl)
                  ((br30 p).mpr ⟨⟨hpar, hH2, hH5⟩, hRSp, hH21, hchain hH21⟩) (by revert l hl; decide)
              · rw [if_neg hLp] at hl
                exact use_row 24 (by decide) (ctx24 s1 hs1 s2 hs2 ⟨hL.not.mp hLp, hRS'⟩) (hmix 24 rfl)
                  ((br24 p).mpr ⟨⟨hpar, hH2, hH5⟩, hRSp, hH21, hchain hH21⟩) (by revert l hl; decide)
