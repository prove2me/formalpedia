-- Prove2me | solution 1 for Freiman.lower_guard_source_run
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T19:33:22.634214+00:00
-- url     : https://prove2.me/submissions/6369616d-0ecc-4605-aa0c-826c6f0d5b0f

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
theorem memR : ∀ r ∈ [row 3, row 5, row 7], ∀ ctx ∈ r.contexts,
    rowCase r ctx ∈ lowerGuardCases := by
  decide +kernel

lemma use_row {p : LowerPair} {s1 s2 : List ℕ+} {l : LowerLabel} (j : ℕ)
    (hj : row j ∈ [row 3, row 5, row 7])
    (hctx : (s1, s2) ∈ (row j).contexts) (hm : (row j).mixed = true ↔ lowerMixed p)
    (hb : lowerGuardBranch (row j).branch p) (hl : l ∈ (row j).labels) :
    ∃ c ∈ lowerGuardCases, (c.before = (s1, s2) ∧ (c.mixed = true ↔ lowerMixed p) ∧
      lowerGuardBranch c.branch p) ∧ l ∈ c.labels :=
  ⟨rowCase (row j) (s1, s2), memR _ hj _ hctx, ⟨rfl, hm, hb⟩, hl⟩

lemma ctxNN : ∀ s1 ∈ lowerGuardStates, ∀ s2 ∈ lowerGuardStates,
    ¬ ([3,1] : List ℕ+) <:+ s1 → ¬ ([3,1] : List ℕ+) <:+ s2 →
    (s1, s2) ∈ (row 3).contexts ∧ (s1, s2) ∈ (row 5).contexts ∧ (s1, s2) ∈ (row 7).contexts := by
  decide
lemma br3 (p : LowerPair) : lowerGuardBranch (row 3).branch p ↔
    ((¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ lowerA p 9) ∧ ¬ lowerL p ∧ ¬ lowerR p ∧ lowerRunOffered p) := Iff.rfl
lemma br5 (p : LowerPair) : lowerGuardBranch (row 5).branch p ↔
    ((¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9) ∧ ¬ lowerL p ∧ ¬ lowerA p 20 ∧ lowerRunOffered p) := Iff.rfl
lemma br7 (p : LowerPair) : lowerGuardBranch (row 7).branch p ↔
    ((¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9) ∧ ¬ lowerL p ∧ lowerA p 20 ∧ lowerRunOffered p) := Iff.rfl
lemma lab (k : ℕ) (hk : 0 < k) (hs : k < 3) :
    (List.replicate k 3, List.replicate k 3) ∈ (row 3).labels ∧
    (List.replicate k 3, List.replicate k 3) ∈ (row 5).labels ∧
    (List.replicate k 3, List.replicate k 3) ∈ (row 7).labels := by
  interval_cases k <;> decide

end M7Guard

open M7Guard in
theorem solution (p : LowerPair) (hp : lowerAdmissible p) (hr : lowerRunOffered p) (k : ℕ) (hk : 0 < k) (hs : k < 3) :
    ∃ c ∈ lowerGuardCases, lowerGuardFits c p ∧ (List.replicate k 3,List.replicate k 3) ∈ c.labels := by
  obtain ⟨hs1, hs2⟩ := states_of_admissible hp
  have hL : lowerL p ↔ ([3,1] : List ℕ+) <:+ lowerGuardState (lowerNormalize p).1 := s31_iff _
  have hR : lowerR p ↔ ([3,1] : List ℕ+) <:+ lowerGuardState (lowerNormalize p).2 := s31_iff _
  obtain ⟨hpar, hA3, hLp, hRp, -⟩ := id hr
  unfold lowerGuardFits
  set s1 := lowerGuardState (lowerNormalize p).1 with hs1def
  set s2 := lowerGuardState (lowerNormalize p).2 with hs2def
  have hmix : ∀ j, (row j).mixed = false → ((row j).mixed = true ↔ lowerMixed p) := by
    intro j h; rw [h]; exact iff_of_false (by decide) hpar
  obtain ⟨hc3, hc5, hc7⟩ := ctxNN s1 hs1 s2 hs2 (hL.not.mp hLp) (hR.not.mp hRp)
  obtain ⟨hl3, hl5, hl7⟩ := lab k hk hs
  by_cases hA9 : lowerA p 9
  · exact use_row 3 (by decide) hc3 (hmix 3 rfl) ((br3 p).mpr ⟨⟨hpar, hA3, hA9⟩, hLp, hRp, hr⟩) hl3
  · by_cases hA20 : lowerA p 20
    · exact use_row 7 (by decide) hc7 (hmix 7 rfl) ((br7 p).mpr ⟨⟨hpar, hA3, hA9⟩, hLp, hA20, hr⟩) hl7
    · exact use_row 5 (by decide) hc5 (hmix 5 rfl) ((br5 p).mpr ⟨⟨hpar, hA3, hA9⟩, hLp, hA20, hr⟩) hl5
