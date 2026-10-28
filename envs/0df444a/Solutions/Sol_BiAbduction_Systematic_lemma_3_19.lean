-- Prove2me | solution 1 for BiAbduction.Systematic.lemma_3_19
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T03:39:41.806033+00:00
-- url     : https://prove2.me/submissions/159e4ce5-15cd-4aeb-a107-f4ac11ad88ed

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Rules

open BiAbduction.Systematic

namespace Lemma319

/-! ## Heaps -/

/-- Graph union of two heaps; total (the domains need not be disjoint). -/
def union (h₀ h₁ : Heap) : Heap where
  cell := fun l => (h₀.cell l).or (h₁.cell l)
  nil_unalloc := by simp [h₀.nil_unalloc, h₁.nil_unalloc]
  finite_dom := by
    refine Set.Finite.subset (h₀.finite_dom.union h₁.finite_dom) ?_
    intro l hl
    simp only [Set.mem_setOf_eq, Set.mem_union] at hl ⊢
    change (h₀.cell l).or (h₁.cell l) ≠ none at hl
    by_contra hc
    push_neg at hc
    exact hl (by rw [hc.1, hc.2]; rfl)

theorem union_cell (h₀ h₁ : Heap) (l : ℕ) : (union h₀ h₁).cell l = (h₀.cell l).or (h₁.cell l) :=
  rfl

/-- The empty heap. -/
def emptyHeap : Heap where
  cell := fun _ => none
  nil_unalloc := rfl
  finite_dom := by
    refine Set.Finite.subset (Set.finite_singleton 0) ?_
    intro l hl
    exact absurd rfl hl

/-- The singleton heap `[l ↦ v]` (empty when `l = 0`). -/
def ptsHeap (l v : ℕ) : Heap where
  cell := fun l' => if l' = l ∧ l ≠ 0 then some v else none
  nil_unalloc := by
    by_cases h : (0 : ℕ) = l
    · subst h; simp
    · simp [h]
  finite_dom := by
    refine Set.Finite.subset (Set.finite_singleton l) ?_
    intro l' hl
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hl ⊢
    by_cases h : l' = l
    · exact h
    · exact absurd (by simp [h]) hl

/-- The heap `h` with the cell at `l` removed. -/
def eraseCell (h : Heap) (l : ℕ) : Heap where
  cell := fun l' => if l' = l then none else h.cell l'
  nil_unalloc := by
    by_cases h0 : (0 : ℕ) = l
    · simp [h0]
    · simp [h0, h.nil_unalloc]
  finite_dom := by
    refine Set.Finite.subset h.finite_dom ?_
    intro l' hl
    simp only [Set.mem_setOf_eq] at hl ⊢
    by_cases h' : l' = l
    · exact absurd (by simp [h']) hl
    · simpa [h'] using hl

theorem ext_cell {h₁ h₂ : Heap} (h : h₁.cell = h₂.cell) : h₁ = h₂ := by
  obtain ⟨c₁, n₁, f₁⟩ := h₁
  obtain ⟨c₂, n₂, f₂⟩ := h₂
  simp only at h
  subst h
  rfl

theorem ptsHeap_cell_self (l v : ℕ) (hl : l ≠ 0) : (ptsHeap l v).cell l = some v :=
  show (if l = l ∧ l ≠ 0 then some v else none) = some v from if_pos ⟨rfl, hl⟩

theorem ptsHeap_cell_of_ne {l l' v : ℕ} (h : l' ≠ l) : (ptsHeap l v).cell l' = none :=
  show (if l' = l ∧ l ≠ 0 then some v else none) = none from if_neg (fun hc => h hc.1)

theorem or_none_eq (x : Option ℕ) : x.or none = x := by cases x <;> rfl

/-- `Heap.IsUnion` as an equation plus disjointness. -/
theorem isUnion_iff {h h₀ h₁ : Heap} :
    Heap.IsUnion h h₀ h₁ ↔ h = union h₀ h₁ ∧ Heap.Disjoint h₀ h₁ := by
  constructor
  · rintro ⟨hd, hc⟩
    exact ⟨ext_cell (funext fun l => hc l), hd⟩
  · rintro ⟨rfl, hd⟩
    exact ⟨hd, fun l => union_cell h₀ h₁ l⟩

theorem isUnion_union {h₀ h₁ : Heap} (hd : Heap.Disjoint h₀ h₁) :
    Heap.IsUnion (union h₀ h₁) h₀ h₁ :=
  isUnion_iff.2 ⟨rfl, hd⟩

theorem disjoint_comm {h₀ h₁ : Heap} (hd : Heap.Disjoint h₀ h₁) : Heap.Disjoint h₁ h₀ :=
  fun l => (hd l).symm

theorem union_swap {h a b : Heap} (hu : Heap.IsUnion h a b) :
    Heap.IsUnion h b a := by
  refine ⟨fun l => (hu.1 l).symm, ?_⟩
  intro l
  rcases hu.1 l with ha | hb
  · simp [hu.2 l, ha]
  · simp [hu.2 l, hb]

theorem disjoint_of_union_left {h₀ h₁ h₂ : Heap} (hd : Heap.Disjoint (union h₀ h₁) h₂) :
    Heap.Disjoint h₀ h₂ := by
  intro l
  rcases hd l with h | h
  · left
    change (h₀.cell l).or (h₁.cell l) = none at h
    cases ha : h₀.cell l <;> cases hb : h₁.cell l <;> simp_all
  · exact Or.inr h

theorem disjoint_of_union_right {h₀ h₁ h₂ : Heap} (hd : Heap.Disjoint (union h₀ h₁) h₂) :
    Heap.Disjoint h₁ h₂ := by
  intro l
  rcases hd l with h | h
  · left
    change (h₀.cell l).or (h₁.cell l) = none at h
    cases ha : h₀.cell l <;> cases hb : h₁.cell l <;> simp_all
  · exact Or.inr h

theorem disjoint_of_union_right' {a x y : Heap} (hd : Heap.Disjoint a (union x y)) :
    Heap.Disjoint a x ∧ Heap.Disjoint a y := by
  constructor
  · intro l
    rcases hd l with h | h
    · exact Or.inl h
    · right
      change (x.cell l).or (y.cell l) = none at h
      cases hx : x.cell l <;> cases hy : y.cell l <;> simp_all
  · intro l
    rcases hd l with h | h
    · exact Or.inl h
    · right
      change (x.cell l).or (y.cell l) = none at h
      cases hx : x.cell l <;> cases hy : y.cell l <;> simp_all

theorem disjoint_of_isUnion_right {a b c d : Heap} (hd : Heap.Disjoint a b)
    (hu : Heap.IsUnion b c d) : Heap.Disjoint a c ∧ Heap.Disjoint a d := by
  obtain ⟨rfl, _⟩ := isUnion_iff.1 hu
  exact disjoint_of_union_right' hd

theorem disjoint_union_right {a x y : Heap} (hax : Heap.Disjoint a x)
    (hay : Heap.Disjoint a y) : Heap.Disjoint a (union x y) := by
  intro l
  by_cases ha : a.cell l = none
  · exact Or.inl ha
  · right
    change (x.cell l).or (y.cell l) = none
    rcases hax l with h | h
    · exact absurd h ha
    · rcases hay l with h' | h'
      · exact absurd h' ha
      · rw [h, h']
        rfl

theorem union_assoc (a b c : Heap) : union (union a b) c = union a (union b c) := by
  refine ext_cell (funext fun l => ?_)
  simp only [union_cell]
  cases a.cell l <;> cases b.cell l <;> cases c.cell l <;> rfl

theorem union_rotate {a b c : Heap} (hab : Heap.Disjoint a b) (hac : Heap.Disjoint a c)
    (hbc : Heap.Disjoint b c) : union a (union b c) = union b (union a c) := by
  refine ext_cell (funext fun l => ?_)
  have h1 : (union a (union b c)).cell l = (a.cell l).or ((b.cell l).or (c.cell l)) := by
    rw [union_cell, union_cell]
  have h2 : (union b (union a c)).cell l = (b.cell l).or ((a.cell l).or (c.cell l)) := by
    rw [union_cell, union_cell]
  rw [h1, h2]
  rcases hab l with h | h <;> rcases hac l with h' | h' <;> rcases hbc l with h'' | h'' <;>
    simp [h, h', h'']

theorem cancel_isUnion_left {a b c d : Heap} (hab : Heap.IsUnion a b c)
    (had : Heap.IsUnion a b d) : c = d := by
  refine ext_cell (funext fun l => ?_)
  by_cases hb : b.cell l = none
  · have h1 := hab.2 l
    have h2 := had.2 l
    rw [hb] at h1 h2
    simpa using h1.symm.trans h2
  · have hc : c.cell l = none := (hab.1 l).resolve_left hb
    have hd : d.cell l = none := (had.1 l).resolve_left hb
    rw [hc, hd]

theorem isUnion_eraseCell {h : Heap} {l v : ℕ} (hv : h.cell l = some v) :
    Heap.IsUnion h (ptsHeap l v) (eraseCell h l) := by
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0, h.nil_unalloc] at hv
    exact absurd hv (by simp)
  refine isUnion_iff.2 ⟨ext_cell (funext fun l' => ?_), ?_⟩
  · rw [union_cell]
    by_cases h' : l' = l
    · show h.cell l' = ((ptsHeap l v).cell l').or (if l' = l then none else h.cell l')
      rw [h', ptsHeap_cell_self l v hl0, if_pos rfl]
      exact hv.trans (or_none_eq (some v)).symm
    · show h.cell l' = ((ptsHeap l v).cell l').or (if l' = l then none else h.cell l')
      rw [ptsHeap_cell_of_ne h', if_neg h']
      rfl
  · intro l'
    by_cases h' : l' = l
    · right; simp [eraseCell, h']
    · left; exact ptsHeap_cell_of_ne h'

theorem union_sub {h a b : Heap} (hu : Heap.IsUnion h a b) : Heap.Subheap a h := by
  intro l v hv
  simpa [hv] using hu.2 l

theorem sub_empty (h : Heap) : Heap.Subheap emptyHeap h := by
  intro l v hv
  exact absurd hv (by simp [emptyHeap])

theorem disjoint_of_sub_right {a b c : Heap} (hd : Heap.Disjoint a c) (hsub : Heap.Subheap b c) :
    Heap.Disjoint a b := by
  intro l
  rcases hd l with ha | hc
  · exact Or.inl ha
  · right
    cases hb : b.cell l with
    | none => rfl
    | some v =>
      have := hsub l v hb
      rw [hc] at this
      exact absurd this (by simp)

theorem union_sub_union_right {v a b : Heap} (hsub : Heap.Subheap a b) :
    Heap.Subheap (union v a) (union v b) := by
  intro l u hu
  rw [union_cell] at hu ⊢
  cases hv : v.cell l with
  | some w =>
    rw [hv] at hu
    exact hu
  | none =>
    rw [hv] at hu
    exact hsub l u hu

theorem sub_split {a h : Heap} (ha : Heap.Subheap a h) :
    ∃ b, Heap.IsUnion h a b := by
  classical
  let b : Heap := {
    cell := fun l => if a.cell l = none then h.cell l else none
    nil_unalloc := by simp [a.nil_unalloc, h.nil_unalloc]
    finite_dom := h.finite_dom.subset (by
      intro l hl
      simp only [Set.mem_setOf_eq] at hl ⊢
      by_contra hn
      simp [hn] at hl) }
  refine ⟨b, ?_, ?_⟩
  · intro l
    by_cases hn : a.cell l = none
    · exact Or.inl hn
    · exact Or.inr (by simp [b, hn])
  · intro l
    cases he : a.cell l with
    | none => simp [b, he]
    | some v => simp [b, he, ha l v he]

theorem spatial_iff (A B : Pred) :
    SpatialLe A B ↔ ∀ p ∈ B, ∃ a : Heap, Heap.Subheap a p.2 ∧ (p.1, a) ∈ A := by
  constructor
  · intro hab p hp
    obtain ⟨a, b, hu, hm, _⟩ := hab hp
    exact ⟨a, union_sub hu, hm⟩
  · intro hab p hp
    obtain ⟨a, ha, hm⟩ := hab p hp
    obtain ⟨b, hu⟩ := sub_split ha
    exact ⟨a, b, hu, hm, Set.mem_univ _⟩

/-! ## Semantic helpers -/

theorem evalE_congr {s s' : Stack} {e : Expr} (h : ∀ x ∈ exprVars e, s' x = s x) :
    evalE s' e = evalE s e := by
  rcases e with x | k
  · simpa [exprVars, evalE] using h x (by simp [exprVars])
  · rfl

theorem ptsDen_congr {pt : PtsTo} {s s' : Stack} {h : Heap}
    (hs : ∀ x ∈ exprVars pt.1 ++ exprVars pt.2, s' x = s x) (hp : (s, h) ∈ ptsDen pt) :
    (s', h) ∈ ptsDen pt := by
  simp only [ptsDen, Set.mem_setOf_eq] at hp ⊢
  have e1 : evalE s' pt.1 = evalE s pt.1 :=
    evalE_congr (fun x hx => hs x (List.mem_append.mpr (Or.inl hx)))
  have e2 : evalE s' pt.2 = evalE s pt.2 :=
    evalE_congr (fun x hx => hs x (List.mem_append.mpr (Or.inr hx)))
  exact ⟨by rw [e1]; exact hp.1, fun l => by rw [e1, e2]; exact hp.2 l⟩

theorem ptsDen_eq_ptsHeap {pt : PtsTo} {s : Stack} {v : Heap} (hv : (s, v) ∈ ptsDen pt) :
    v = ptsHeap (evalE s pt.1) (evalE s pt.2) := by
  obtain ⟨hne, hcell⟩ := hv
  refine ext_cell (funext fun l => ?_)
  rw [hcell l]
  by_cases hl : l = evalE s pt.1
  · subst hl
    simp [ptsHeap, hne]
  · simp [ptsHeap, hl]

theorem pureDen_congr {pi : List PureAtom} {s s' : Stack} {h : Heap}
    (hs : ∀ x ∈ pureVars pi, s' x = s x) (hp : (s, h) ∈ pureDen pi) : (s', h) ∈ pureDen pi := by
  intro a ha
  have hv : ∀ x ∈ exprVars a.2.1 ++ exprVars a.2.2, s' x = s x := by
    intro x hx
    refine hs x ?_
    show x ∈ pi.flatMap (fun a => exprVars a.2.1 ++ exprVars a.2.2)
    exact List.mem_flatMap.mpr ⟨a, ha, hx⟩
  have e1 := evalE_congr (e := a.2.1) (fun x hx => hv x (List.mem_append.mpr (Or.inl hx)))
  have e2 := evalE_congr (e := a.2.2) (fun x hx => hv x (List.mem_append.mpr (Or.inr hx)))
  have hpa := hp a ha
  simp only [atomHolds] at hpa ⊢
  rw [e1, e2]
  exact hpa

theorem pureDen_snd {pi : List PureAtom} {s : Stack} {h h' : Heap}
    (hp : (s, h) ∈ pureDen pi) : (s, h') ∈ pureDen pi := by
  simpa only [pureDen, Set.mem_setOf_eq] using hp

theorem spatialDen_cons (pt : PtsTo) (sig : List PtsTo) (tr : Bool) :
    spatialDen (pt :: sig) tr = sepConj (ptsDen pt) (spatialDen sig tr) := rfl

theorem spatialDen_congr : ∀ (sig : List PtsTo) (tr : Bool) {s s' : Stack} {h : Heap},
    (∀ x ∈ ptsVars sig, s' x = s x) → (s, h) ∈ spatialDen sig tr →
      (s', h) ∈ spatialDen sig tr := by
  intro sig
  induction sig with
  | nil =>
    intro tr s s' h hs hh
    simpa [spatialDen, emp] using hh
  | cons a rest ih =>
    intro tr s s' h hs hh
    rw [spatialDen_cons] at hh ⊢
    obtain ⟨h₀, h₁, hu, h0, h1⟩ := hh
    have hs1 : ∀ x ∈ exprVars a.1 ++ exprVars a.2, s' x = s x := by
      intro x hx
      refine hs x ?_
      show x ∈ (a :: rest).flatMap (fun pt => exprVars pt.1 ++ exprVars pt.2)
      exact List.mem_flatMap.mpr ⟨a, List.mem_cons.mpr (Or.inl rfl), hx⟩
    have hs2 : ∀ x ∈ ptsVars rest, s' x = s x := by
      intro x hx
      obtain ⟨pt, hmem, hx'⟩ := List.mem_flatMap.1 hx
      refine hs x ?_
      show x ∈ (a :: rest).flatMap (fun pt => exprVars pt.1 ++ exprVars pt.2)
      exact List.mem_flatMap.mpr ⟨pt, List.mem_cons.mpr (Or.inr hmem), hx'⟩
    exact ⟨h₀, h₁, hu, ptsDen_congr hs1 h0, ih tr hs2 h1⟩

def qVars (q : QF) : List ℕ := pureVars q.1 ++ ptsVars q.2.1

theorem qfDen_congr {q : QF} {s s' : Stack} {h : Heap}
    (hs : ∀ x ∈ qVars q, s' x = s x) (hp : (s, h) ∈ qfDen q) : (s', h) ∈ qfDen q := by
  obtain ⟨hp1, hp2⟩ := hp
  refine ⟨pureDen_congr ?_ hp1, spatialDen_congr q.2.1 q.2.2 ?_ hp2⟩
  · intro x hx
    exact hs x (List.mem_append.mpr (Or.inl hx))
  · intro x hx
    exact hs x (List.mem_append.mpr (Or.inr hx))

theorem lhsDen_congr {Δ : LHS} {s s' : Stack} {h : Heap}
    (hs : ∀ x ∈ lhsVars Δ, s' x = s x) (hp : (s, h) ∈ lhsDen Δ) : (s', h) ∈ lhsDen Δ :=
  qfDen_congr (q := (Δ.1, Δ.2, false)) hs hp

theorem conv_nil {Δ : LHS} {q : QF} : Conv Δ ([], q) := fun x hx => by simp at hx

/-! ## `spatialDen` properties -/

theorem get_cons_zero' (a : PtsTo) (rest : List PtsTo) :
    (a :: rest).get (0 : Fin (a :: rest).length) = a := List.get_cons_zero ..

theorem get_cons_succ' {a : PtsTo} {rest : List PtsTo} (k : Fin rest.length) :
    (a :: rest).get k.succ = rest.get k := List.get_cons_succ ..

/-- A heap satisfying `Σ` splits at any of its points-to facts. -/
theorem spatialDen_split : ∀ (sig : List PtsTo) (tr : Bool) (s : Stack) (h : Heap)
    (j : Fin sig.length), (s, h) ∈ spatialDen sig tr →
      ∃ v w, Heap.IsUnion h v w ∧ (s, v) ∈ ptsDen (sig.get j) ∧
        (s, w) ∈ spatialDen (sig.eraseIdx j) tr := by
  intro sig
  induction sig with
  | nil =>
    intro tr s h j _
    exact absurd j.isLt (Nat.not_lt_zero j.1)
  | cons a rest ih =>
    intro tr s h j hh
    rw [spatialDen_cons] at hh
    obtain ⟨h₀, h₁, hu, h0, h1⟩ := hh
    cases j using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, List.eraseIdx_cons_zero]
      exact ⟨h₀, h₁, hu, h0, h1⟩
    | succ j' =>
      simp only [Fin.val_succ, List.eraseIdx_cons_succ]
      have hu' : Heap.IsUnion h h₀ h₁ := hu
      obtain ⟨v, w, hu1, hv, hw⟩ := ih tr s h₁ j' h1
      obtain ⟨hc1, hd1⟩ := isUnion_iff.1 hu1
      obtain ⟨hc, hd⟩ := isUnion_iff.1 hu'
      have h0v : Heap.Disjoint h₀ v := (disjoint_of_isUnion_right hd hu1).1
      have h0w : Heap.Disjoint h₀ w := (disjoint_of_isUnion_right hd hu1).2
      refine ⟨v, union h₀ w, isUnion_iff.2 ⟨?_, ?_⟩, hv, ?_⟩
      · rw [hc, hc1]
        exact union_rotate h0v h0w hd1
      · exact disjoint_union_right (disjoint_comm h0v) hd1
      · rw [spatialDen_cons]
        exact ⟨h₀, w, isUnion_union h0w, h0, hw⟩

/-- The cell prescribed by the `k`-th points-to fact is the one the heap carries. -/
theorem spatialDen_cell : ∀ (sig : List PtsTo) (tr : Bool) (s : Stack) (h : Heap)
    (k : Fin sig.length), (s, h) ∈ spatialDen sig tr →
      h.cell (evalE s (sig.get k).1) = some (evalE s (sig.get k).2) := by
  intro sig
  induction sig with
  | nil => intro tr s h k _; exact absurd k.isLt (Nat.not_lt_zero k.1)
  | cons a rest ih =>
    intro tr s h k hh
    rw [spatialDen_cons] at hh
    obtain ⟨h₀, h₁, hu, h0, h1⟩ := hh
    obtain ⟨hd, hc⟩ := hu
    cases k using Fin.cases with
    | zero =>
      rw [get_cons_zero']
      have h0' : h₀.cell (evalE s a.1) = some (evalE s a.2) := by
        have h2 := h0
        simp only [ptsDen, Set.mem_setOf_eq] at h2
        simpa using h2.2 (evalE s a.1)
      rw [hc (evalE s a.1), h0']
      simp
    | succ i =>
      rw [get_cons_succ']
      have h1' : h₁.cell (evalE s (rest.get i).1) = some (evalE s (rest.get i).2) :=
        ih tr s h₁ i h1
      rcases hd (evalE s (rest.get i).1) with hd0 | hd1
      · rw [hc (evalE s (rest.get i).1), hd0, h1']
        simp
      · rw [h1'] at hd1
        exact absurd hd1 (by simp)

/-- Every allocated cell in a heap satisfying `spatialDen sig false` comes from some entry of `sig`. -/
theorem spatialDen_find_cell : ∀ (sig : List PtsTo) (s : Stack) (h : Heap) (l₀ v₀ : ℕ),
    (s, h) ∈ spatialDen sig false → h.cell l₀ = some v₀ →
      ∃ j : Fin sig.length, evalE s (sig.get j).1 = l₀ ∧ evalE s (sig.get j).2 = v₀ := by
  intro sig
  induction sig with
  | nil =>
    intro s h l₀ v₀ hh hcell
    have hemp : h.cell l₀ = none := hh l₀
    rw [hemp] at hcell
    exact absurd hcell (by simp)
  | cons a rest ih =>
    intro s h l₀ v₀ hh hcell
    rw [spatialDen_cons] at hh
    obtain ⟨h₀, h₁, hu, h0, h1⟩ := hh
    have hc := hu.2 l₀
    have h0cell : h₀.cell l₀ = if l₀ = evalE s a.1 then some (evalE s a.2) else none := h0.2 l₀
    by_cases hl : l₀ = evalE s a.1
    · rw [if_pos hl] at h0cell
      rw [hcell, h0cell] at hc
      have hv : evalE s a.2 = v₀ := by simpa using hc.symm
      refine ⟨0, ?_, ?_⟩
      · rw [get_cons_zero']; exact hl.symm
      · rw [get_cons_zero']; exact hv
    · rw [if_neg hl] at h0cell
      rw [hcell, h0cell] at hc
      have h1cell : h₁.cell l₀ = some v₀ := by simpa using hc.symm
      obtain ⟨j', hj1, hj2⟩ := ih s h₁ l₀ v₀ h1 h1cell
      refine ⟨j'.succ, ?_, ?_⟩
      · rw [get_cons_succ']; exact hj1
      · rw [get_cons_succ']; exact hj2

/-! ## Bindings and `∃`-quantification -/

theorem binders_empty : ∀ {Δ : LHS} {D : Disj} {H : SH}, Derives Δ D H → H.1 = [] →
    ∀ Hd ∈ D, Hd.1 = [] := by
  intro Δ D H hder
  induction hder with
  | false_ax pi sig pi' hsig =>
    intro _ Hd hmem
    simp at hmem
  | emp_ax pi pi' =>
    intro _ Hd hmem
    rw [List.mem_singleton] at hmem
    rw [hmem]
  | true_ax pi sig pi' =>
    intro _ Hd hmem
    rw [List.mem_singleton] at hmem
    rw [hmem]
  | psto pi sig pi' sig' tr k Ds D hj hd ihj ihd =>
    intro _ Hd hmem
    rcases List.mem_append.1 hmem with hmem | hmem
    · obtain ⟨j, _, hmemj⟩ := List.mem_flatMap.1 hmem
      obtain ⟨Hd0, hmem0, rfl⟩ := List.mem_map.1 hmemj
      exact ihj j rfl Hd0 hmem0
    · obtain ⟨Hd0, hmem0, rfl⟩ := List.mem_map.1 hmem
      exact ihd rfl Hd0 hmem0
  | exists_r Δ D q X h ih =>
    intro hX Hd hmem
    have hX' : X = [] := hX
    subst hX'
    obtain ⟨Hd0, hmem0, rfl⟩ := List.mem_map.1 hmem
    have := ih rfl Hd0 hmem0
    simpa [bindVars] using this

theorem mem_foldr_exQ_of_mem {F : Pred} : ∀ {X : List ℕ} {p : State},
    p ∈ X.foldr exQ F → ∃ s' : Stack, (∀ x ∉ X, s' x = p.1 x) ∧ (s', p.2) ∈ F := by
  intro X
  induction X with
  | nil =>
    intro p hp
    exact ⟨p.1, by simp, hp⟩
  | cons x xs ih =>
    intro p hp
    rw [List.foldr_cons] at hp
    obtain ⟨v, hv⟩ := hp
    obtain ⟨s', hs', hsF⟩ := ih hv
    refine ⟨s', ?_, hsF⟩
    intro y hy
    have hyx : y ≠ x := fun hc => hy (List.mem_cons.mpr (Or.inl hc))
    have hy' : y ∉ xs := fun hc => hy (List.mem_cons.mpr (Or.inr hc))
    have h1 : s' y = (Function.update p.1 x v) y := hs' y hy'
    have h2 : (Function.update p.1 x v) y = p.1 y := by simp [Function.update, hyx]
    rw [h1, h2]

theorem mem_foldr_exQ_qf : ∀ {q : QF} {X : List ℕ} {s s' : Stack} {h : Heap},
    (∀ x ∈ qVars q, x ∉ X → s' x = s x) → (s', h) ∈ qfDen q →
      (s, h) ∈ X.foldr exQ (qfDen q) := by
  intro q X
  induction X with
  | nil =>
    intro s s' h hs hp
    exact qfDen_congr (q := q) (s := s') (s' := s) (fun x hx => (hs x hx (by simp)).symm) hp
  | cons x xs ih =>
    intro s s' h hs hp
    rw [List.foldr_cons]
    refine ⟨s' x, ?_⟩
    refine ih (s := Function.update s x (s' x)) (s' := s') ?_ hp
    intro y hyq hy
    by_cases hyx : y = x
    · subst hyx
      simp [Function.update]
    · have : y ∉ x :: xs := by
        intro hc
        rcases List.mem_cons.1 hc with hc' | hc'
        · exact hyx hc'
        · exact hy hc'
      have h1 := hs y hyq this
      have h2 : (Function.update s x (s' x)) y = s y := by simp [Function.update, hyx]
      rw [h1, h2]

/-! ## Inductive completeness of `Derives` -/

theorem derives_complete_aux {Δ : LHS} {D : Disj} {H : SH} (hder : Derives Δ D H) :
    Conv Δ H → ∀ (s : Stack) (h_Δ h_F : Heap),
      Heap.Disjoint h_Δ h_F → (s, h_Δ) ∈ lhsDen Δ → (s, union h_Δ h_F) ∈ shDen H →
        ∃ h_D : Heap, Heap.Subheap h_D h_F ∧ (s, h_D) ∈ disjDen D := by
  induction hder with
  | false_ax pi sig pi' hsig =>
    intro _ s h_Δ h_F _ hΔ hH
    exfalso
    have hsa : (s, h_Δ) ∈ spatialDen sig false := hΔ.2
    have hemp : ∀ l, (union h_Δ h_F).cell l = none := hH.2
    have hpos : 0 < sig.length := List.length_pos_iff.mpr hsig
    let k0 : Fin sig.length := ⟨0, hpos⟩
    have hc := spatialDen_cell sig false s h_Δ k0 hsa
    have hu := hemp (evalE s (sig.get k0).1)
    rw [union_cell, hc] at hu
    exact absurd hu (by simp)
  | emp_ax pi pi' =>
    intro _ s h_Δ h_F _ _ hH
    refine ⟨emptyHeap, sub_empty h_F, ?_⟩
    refine ⟨([], (pi', [], false)), List.mem_singleton.mpr rfl, ?_⟩
    exact ⟨pureDen_snd hH.1, fun _ => rfl⟩
  | true_ax pi sig pi' =>
    intro _ s h_Δ h_F _ _ hH
    refine ⟨emptyHeap, sub_empty h_F, ?_⟩
    refine ⟨([], (pi', [], false)), List.mem_singleton.mpr rfl, ?_⟩
    exact ⟨pureDen_snd hH.1, fun _ => rfl⟩
  | psto pi sig pi' sig' tr k Ds D hj hd ihj ihd =>
    intro _ s h_Δ h_F hd_Δ_F hΔ hH
    obtain ⟨hpa, hsa⟩ := hΔ
    obtain ⟨hp', hsp'⟩ := hH
    obtain ⟨v, w, huvw, hv, hw⟩ := spatialDen_split sig' tr s (union h_Δ h_F) k hsp'
    let l₀ := evalE s (sig'.get k).1
    let v₀ := evalE s (sig'.get k).2
    have hv_pts : v = ptsHeap l₀ v₀ := ptsDen_eq_ptsHeap hv
    have hl₀ : l₀ ≠ 0 := hv.1
    have hv_l₀ : v.cell l₀ = some v₀ := by
      rw [hv_pts]
      exact ptsHeap_cell_self l₀ v₀ hl₀
    have hu_l₀ : (union h_Δ h_F).cell l₀ = some v₀ := by
      have hc := huvw.2 l₀
      rw [hv_l₀] at hc
      exact hc
    cases hcell_Δ : h_Δ.cell l₀ with
    | some u =>
      have hu_eq : u = v₀ := by
        rw [union_cell, hcell_Δ] at hu_l₀
        exact Option.some.inj hu_l₀
      subst hu_eq
      obtain ⟨j, hej1, hej2⟩ := spatialDen_find_cell sig s h_Δ l₀ v₀ hsa hcell_Δ
      obtain ⟨v', h_Δ', hu_Δ, hv', h_Δ'_sp⟩ := spatialDen_split sig false s h_Δ j hsa
      have hv'_eq : v' = v := by
        rw [ptsDen_eq_ptsHeap hv', hv_pts, hej1, hej2]
      rw [hv'_eq] at hu_Δ
      obtain ⟨hc_Δ, hd_v_Δ'⟩ := isUnion_iff.1 hu_Δ
      have hd_v_Δ'_F : Heap.Disjoint (union v h_Δ') h_F := by
        rw [← hc_Δ]; exact hd_Δ_F
      have hd_v_F : Heap.Disjoint v h_F := disjoint_of_union_left hd_v_Δ'_F
      have hd_Δ'_F : Heap.Disjoint h_Δ' h_F := disjoint_of_union_right hd_v_Δ'_F
      have hu_all : Heap.IsUnion (union h_Δ h_F) v (union h_Δ' h_F) :=
        isUnion_iff.2 ⟨by rw [hc_Δ, union_assoc], disjoint_union_right hd_v_Δ' hd_v_F⟩
      have hw_eq : w = union h_Δ' h_F := cancel_isUnion_left huvw hu_all
      have hΔ' : (s, h_Δ') ∈ lhsDen (pi, sig.eraseIdx j) := ⟨pureDen_snd hpa, h_Δ'_sp⟩
      have hH' : (s, union h_Δ' h_F) ∈ shDen ([], (pi', sig'.eraseIdx k, tr)) := by
        refine ⟨pureDen_snd hp', ?_⟩
        rw [← hw_eq]
        exact hw
      obtain ⟨h_D, hsub, hmemD⟩ := ihj j conv_nil s h_Δ' h_F hd_Δ'_F hΔ' hH'
      obtain ⟨Hd0, hmem0, hsh0⟩ := hmemD
      have hb0 : Hd0.1 = [] := binders_empty (hj j) rfl Hd0 hmem0
      have hqf0 : (s, h_D) ∈ qfDen Hd0.2 := by
        simpa [shDen, hb0] using hsh0
      refine ⟨h_D, hsub, ?_⟩
      let atoms := [(true, (sig.get j).1, (sig'.get k).1),
                    (true, (sig.get j).2, (sig'.get k).2)]
      refine ⟨addAtoms atoms Hd0, ?_, ?_⟩
      · refine List.mem_append.mpr (Or.inl ?_)
        refine List.mem_flatMap.mpr ⟨j, List.mem_finRange j, ?_⟩
        exact List.mem_map.mpr ⟨Hd0, hmem0, rfl⟩
      · simp only [shDen, addAtoms, hb0, List.foldr_nil]
        refine ⟨?_, hqf0.2⟩
        intro a ha
        rcases List.mem_append.1 ha with ha | ha
        · simp only [atoms, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · exact hej1
          · exact hej2
        · exact hqf0.1 a ha
    | none =>
      have hcell_F : h_F.cell l₀ = some v₀ := by
        rw [union_cell, hcell_Δ] at hu_l₀
        exact hu_l₀
      let h_F' := eraseCell h_F l₀
      have hu_F : Heap.IsUnion h_F v h_F' := by
        rw [hv_pts]
        exact isUnion_eraseCell hcell_F
      obtain ⟨hc_F, hd_v_F'⟩ := isUnion_iff.1 hu_F
      have hd_Δ_v : Heap.Disjoint h_Δ v := (disjoint_of_isUnion_right hd_Δ_F hu_F).1
      have hd_Δ_F' : Heap.Disjoint h_Δ h_F' := (disjoint_of_isUnion_right hd_Δ_F hu_F).2
      have hu_all : Heap.IsUnion (union h_Δ h_F) v (union h_Δ h_F') :=
        isUnion_iff.2 ⟨by rw [hc_F, union_rotate hd_Δ_v hd_Δ_F' hd_v_F'],
          disjoint_union_right (disjoint_comm hd_Δ_v) hd_v_F'⟩
      have hw_eq : w = union h_Δ h_F' := cancel_isUnion_left huvw hu_all
      have hH' : (s, union h_Δ h_F') ∈ shDen ([], (pi', sig'.eraseIdx k, tr)) := by
        refine ⟨pureDen_snd hp', ?_⟩
        rw [← hw_eq]
        exact hw
      obtain ⟨h_D', hsub', hmemD'⟩ := ihd conv_nil s h_Δ h_F' hd_Δ_F' ⟨hpa, hsa⟩ hH'
      obtain ⟨Hd0, hmem0, hsh0⟩ := hmemD'
      have hb0 : Hd0.1 = [] := binders_empty hd rfl Hd0 hmem0
      have hqf0 : (s, h_D') ∈ qfDen Hd0.2 := by
        simpa [shDen, hb0] using hsh0
      have hd_v_D' : Heap.Disjoint v h_D' := disjoint_of_sub_right hd_v_F' hsub'
      have hsub_union : Heap.Subheap (union v h_D') h_F := by
        rw [hc_F]
        exact union_sub_union_right hsub'
      refine ⟨union v h_D', hsub_union, ?_⟩
      refine ⟨addPts (sig'.get k) Hd0, ?_, ?_⟩
      · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨Hd0, hmem0, rfl⟩))
      · simp only [shDen, addPts, hb0, List.foldr_nil]
        refine ⟨pureDen_snd hqf0.1, ?_⟩
        rw [spatialDen_cons]
        exact ⟨v, h_D', isUnion_union hd_v_D', hv, hqf0.2⟩
  | exists_r Δ D q X h ih =>
    intro hconv s h_Δ h_F hd_Δ_F hΔ hH
    obtain ⟨s', hs', hq'⟩ := mem_foldr_exQ_of_mem hH
    have hΔ' : (s', h_Δ) ∈ lhsDen Δ := by
      refine lhsDen_congr (s := s) ?_ hΔ
      intro x hx
      exact hs' x (fun hc => hconv x hc hx)
    obtain ⟨h_D, hsub, hmemD⟩ := ih conv_nil s' h_Δ h_F hd_Δ_F hΔ' hq'
    obtain ⟨Hd0, hmem0, hsh0⟩ := hmemD
    have hb0 : Hd0.1 = [] := binders_empty h rfl Hd0 hmem0
    have hqf0 : (s', h_D) ∈ qfDen Hd0.2 := by
      simpa [shDen, hb0] using hsh0
    refine ⟨h_D, hsub, ?_⟩
    refine ⟨bindVars X Hd0, List.mem_map.mpr ⟨Hd0, hmem0, rfl⟩, ?_⟩
    have hbX : (s, h_D) ∈ X.foldr exQ (qfDen Hd0.2) := by
      refine mem_foldr_exQ_qf (q := Hd0.2) (X := X) (s := s) (s' := s') ?_ hqf0
      intro x _ hxX
      exact hs' x hxX
    simpa [shDen, bindVars, hb0] using hbX

theorem solution (Δ : LHS) (D : Disj) (H : SH) (hconv : Conv Δ H)
    (hder : Derives Δ D H) (F : Pred) (hF : IsSolution (lhsDen Δ) (shDen H) F) :
    CompatLe (lhsDen Δ) (disjDen D) F := by
  rw [CompatLe, spatial_iff]
  rintro ⟨s, h_F⟩ ⟨hpF, hpE⟩
  have hex : ∃ h_Δ hu : Heap, Heap.IsUnion hu h_F h_Δ ∧ (s, h_Δ) ∈ lhsDen Δ := by
    by_contra hno
    exact hpE (fun h_Δ hu hu_F_Δ hΔ => hno ⟨h_Δ, hu, hu_F_Δ, hΔ⟩)
  obtain ⟨h_Δ, hu, hu_F_Δ, hΔ⟩ := hex
  have hu_Δ_F : Heap.IsUnion hu h_Δ h_F := union_swap hu_F_Δ
  obtain ⟨hc_u, hd_Δ_F⟩ := isUnion_iff.1 hu_Δ_F
  have hH : (s, union h_Δ h_F) ∈ shDen H := by
    rw [← hc_u]
    exact hF ⟨h_Δ, h_F, hu_Δ_F, hΔ, hpF⟩
  obtain ⟨h_D, hsub, hmemD⟩ := derives_complete_aux hder hconv s h_Δ h_F hd_Δ_F hΔ hH
  refine ⟨h_D, hsub, hmemD, ?_⟩
  show (s, h_D) ∈ Elsewhere (lhsDen Δ)
  intro hwand
  have hd_D_Δ : Heap.Disjoint h_D h_Δ :=
    disjoint_comm (disjoint_of_sub_right hd_Δ_F hsub)
  exact hwand h_Δ (union h_D h_Δ) (isUnion_union hd_D_Δ) hΔ

end Lemma319

theorem solution (Δ : LHS) (D : Disj) (H : SH) (hconv : Conv Δ H)
    (hder : Derives Δ D H) (F : Pred) (hF : IsSolution (lhsDen Δ) (shDen H) F) :
    CompatLe (lhsDen Δ) (disjDen D) F :=
  Lemma319.solution Δ D H hconv hder F hF
