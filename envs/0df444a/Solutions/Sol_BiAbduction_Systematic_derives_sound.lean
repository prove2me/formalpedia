-- Prove2me | solution 1 for BiAbduction.Systematic.derives_sound
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T11:36:28.896886+00:00
-- url     : https://prove2.me/submissions/941e751a-b5e4-4aa8-85b0-4cfb98150c9a

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Rules

open BiAbduction.Systematic

/-!
`derives_sound` (§3.4.2, p. 28): the rules of Figure 2 derive a solution of the abduction
question (5).

The judgment `Δ ∗ [D] ⊨ H` (`IsSolution (lhsDen Δ) (shDen H) (disjDen D)`) is proved by
induction on the derivation.  The only interesting cases are `psto` (which needs the split and
insert lemmas for `spatialDen`) and `exists_r` (which needs the characterisation of
`foldr exQ`).
-/

namespace Soundness89

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

theorem ext_cell {h₁ h₂ : Heap} (h : h₁.cell = h₂.cell) : h₁ = h₂ := by
  obtain ⟨c₁, n₁, f₁⟩ := h₁
  obtain ⟨c₂, n₂, f₂⟩ := h₂
  simp only at h
  subst h
  rfl

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

theorem disjoint_union {h₀ h₁ h₂ : Heap} (h₀₂ : Heap.Disjoint h₀ h₂)
    (h₁₂ : Heap.Disjoint h₁ h₂) : Heap.Disjoint (union h₀ h₁) h₂ := by
  intro l
  rcases h₀₂ l with h | h
  · rcases h₁₂ l with h' | h'
    · left
      change (h₀.cell l).or (h₁.cell l) = none
      rw [h, h']
      rfl
    · exact Or.inr h'
  · exact Or.inr h

/-- Disjointness from a state of one heap into both parts of a union. -/
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

/-- Disjointness transfer along a decomposition. -/
theorem disjoint_of_isUnion_right {a b c d : Heap} (hd : Heap.Disjoint a b)
    (hu : Heap.IsUnion b c d) : Heap.Disjoint a c ∧ Heap.Disjoint a d := by
  obtain ⟨rfl, _⟩ := isUnion_iff.1 hu
  exact disjoint_of_union_right' hd

/-- Disjointness from a heap into a union of two heaps. -/
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

theorem union_empty_left (a : Heap) : union emptyHeap a = a := by
  refine ext_cell (funext fun l => ?_)
  rw [union_cell]
  show (none : Option ℕ).or (a.cell l) = a.cell l
  cases a.cell l <;> rfl

/-- For three pairwise disjoint heaps the union of the two orders agree. -/
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

/-- `ptsDen` only depends on the values of the two expressions. -/
theorem ptsDen_of_eval_eq {pt pt' : PtsTo} {s : Stack} {h : Heap}
    (h1 : evalE s pt.1 = evalE s pt'.1) (h2 : evalE s pt.2 = evalE s pt'.2)
    (hp : (s, h) ∈ ptsDen pt) : (s, h) ∈ ptsDen pt' := by
  simp only [ptsDen, Set.mem_setOf_eq] at hp ⊢
  exact ⟨by rw [← h1]; exact hp.1, fun l => by rw [← h1, ← h2]; exact hp.2 l⟩

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

/-- `pureDen` does not look at the heap. -/
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

/-- The variables a quantifier-free formula can depend on. -/
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

/-! ## `spatialDen` split and insert -/

theorem get_cons_zero' (a : PtsTo) (rest : List PtsTo) :
    (a :: rest).get (0 : Fin (a :: rest).length) = a := List.get_cons_zero ..

theorem get_cons_succ' {a : PtsTo} {rest : List PtsTo} (k : Fin rest.length) :
    (a :: rest).get k.succ = rest.get k := List.get_cons_succ ..

/-- A heap satisfying `Σ` splits at any of its points-to facts. -/
theorem spatialDen_split : ∀ (sig : List PtsTo) (s : Stack) (h : Heap) (j : Fin sig.length),
    (s, h) ∈ spatialDen sig false →
      ∃ v w, Heap.IsUnion h v w ∧ (s, v) ∈ ptsDen (sig.get j) ∧
        (s, w) ∈ spatialDen (sig.eraseIdx j) false := by
  intro sig
  induction sig with
  | nil =>
    intro s h j _
    exact absurd j.isLt (Nat.not_lt_zero j.1)
  | cons a rest ih =>
    intro s h j hh
    rw [spatialDen_cons] at hh
    obtain ⟨h₀, h₁, hu, h0, h1⟩ := hh
    cases j using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, List.eraseIdx_cons_zero]
      exact ⟨h₀, h₁, hu, h0, h1⟩
    | succ j' =>
      simp only [Fin.val_succ, List.eraseIdx_cons_succ]
      have hu' : Heap.IsUnion h h₀ h₁ := hu
      obtain ⟨v, w, hu1, hv, hw⟩ := ih s h₁ j' h1
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

/-- A heap satisfying `Σ` with the `k`-th cell removed can be extended by it. -/
theorem spatialDen_insert : ∀ (sig : List PtsTo) (tr : Bool) (s : Stack) (v h : Heap)
    (k : Fin sig.length), (s, v) ∈ ptsDen (sig.get k) →
      (s, h) ∈ spatialDen (sig.eraseIdx k) tr → Heap.Disjoint v h →
        (s, union v h) ∈ spatialDen sig tr := by
  intro sig
  induction sig with
  | nil =>
    intro tr s v h k _ _ _
    exact absurd k.isLt (Nat.not_lt_zero k.1)
  | cons a rest ih =>
    intro tr s v h k hv hh hd
    cases k using Fin.cases with
    | zero =>
      rw [get_cons_zero'] at hv
      simp only [Fin.val_zero, List.eraseIdx_cons_zero, spatialDen_cons]
      exact ⟨v, h, isUnion_union hd, hv, hh⟩
    | succ k' =>
      rw [get_cons_succ'] at hv
      simp only [Fin.val_succ, List.eraseIdx_cons_succ, spatialDen_cons] at hh
      obtain ⟨h₀, h₁, hu, h0, h1⟩ := hh
      have hu' : Heap.IsUnion h h₀ h₁ := hu
      obtain ⟨hc01, hd01⟩ := isUnion_iff.1 hu'
      have hdv1 : Heap.Disjoint v h₁ := (disjoint_of_isUnion_right hd hu').2
      have hdv0 : Heap.Disjoint h₀ v := disjoint_comm (disjoint_of_isUnion_right hd hu').1
      have hI := ih tr s v h₁ k' hv h1 hdv1
      rw [spatialDen_cons]
      refine ⟨h₀, union v h₁, isUnion_iff.2 ⟨?_, ?_⟩, h0, hI⟩
      · rw [hc01]
        exact union_rotate (disjoint_comm hdv0) hdv1 hd01
      · exact disjoint_union_right hdv0 hd01

/-- The insert lemma in terms of a decomposition of the heap. -/
theorem spatialDen_insert_of_isUnion {sig : List PtsTo} {tr : Bool} {s : Stack} {v h h' : Heap}
    {k : Fin sig.length} (hv : (s, v) ∈ ptsDen (sig.get k))
    (hh : (s, h') ∈ spatialDen (sig.eraseIdx k) tr) (hu : Heap.IsUnion h v h') :
    (s, h) ∈ spatialDen sig tr := by
  obtain ⟨hc, hd⟩ := isUnion_iff.1 hu
  rw [hc]
  exact spatialDen_insert sig tr s v h' k hv hh hd

/-! ## Bindings and `∃`-quantification -/

/-- If the conclusion binds nothing, neither does any disjunct of the abduction. -/
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

/-- Membership in `foldr exQ` gives a stack that agrees with the original one outside the
quantified variables. -/
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

/-- Conversely a state of `qfDen q` at a stack that only differs on the quantified variables
gives a state of the quantified formula. -/
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

/-! ## The soundness theorem -/

theorem solution (Δ : LHS) (D : Disj) (H : SH) (hconv : Conv Δ H) (hder : Derives Δ D H) :
    IsSolution (lhsDen Δ) (shDen H) (disjDen D) := by
  revert hconv
  induction hder with
  | false_ax pi sig pi' hsig =>
    intro _
    rintro p ⟨a, b, hu, ha, hb⟩
    simp [disjDen] at hb
  | emp_ax pi pi' =>
    intro _
    rintro p ⟨a, b, hu, ha, hb⟩
    have hb' : (p.1, b) ∈ qfDen (pi', [], false) := by
      simpa [disjDen, shDen] using hb
    have ha' : ∀ l, a.cell l = none := by
      intro l
      exact ha.2 l
    have hb'' : ∀ l, b.cell l = none := by
      intro l
      exact hb'.2 l
    refine ⟨hb'.1, ?_⟩
    intro l
    simp [hu.2 l, ha' l, hb'' l]
  | true_ax pi sig pi' =>
    intro _
    rintro p ⟨a, b, hu, ha, hb⟩
    have hb' : (p.1, b) ∈ qfDen (pi', [], false) := by
      simpa [disjDen, shDen] using hb
    exact ⟨hb'.1, Set.mem_univ _⟩
  | psto pi sig pi' sig' tr k Ds D hj hd ihj ihd =>
    intro _ p hp
    obtain ⟨h_a, h_b, hu, ha, hb⟩ := hp
    obtain ⟨hpa, hsa⟩ := ha
    obtain ⟨hcab, hdab⟩ := isUnion_iff.1 hu
    rcases hb with ⟨Hd, hmem, hbden⟩
    rcases List.mem_append.1 hmem with hmem | hmem
    · -- first disjunct: one of the `D_j` with the equalities `L_j = L'_k`, `R_j = R'_k`
      obtain ⟨j, _, hmemj⟩ := List.mem_flatMap.1 hmem
      obtain ⟨Hd0, hmem0, rfl⟩ := List.mem_map.1 hmemj
      have hb0 : Hd0.1 = [] := binders_empty (hj j) rfl Hd0 hmem0
      have hbq : (p.1, h_b) ∈ qfDen ((true, (sig.get j).1, (sig'.get k).1) ::
          (true, (sig.get j).2, (sig'.get k).2) :: Hd0.2.1, Hd0.2.2.1, Hd0.2.2.2) := by
        simpa [shDen, addAtoms, hb0] using hbden
      obtain ⟨hatoms, hbody⟩ := hbq
      have heq1 : evalE p.1 (sig.get j).1 = evalE p.1 (sig'.get k).1 := by
        have := hatoms (true, (sig.get j).1, (sig'.get k).1) (by simp)
        simpa [atomHolds] using this
      have heq2 : evalE p.1 (sig.get j).2 = evalE p.1 (sig'.get k).2 := by
        have := hatoms (true, (sig.get j).2, (sig'.get k).2) (by simp)
        simpa [atomHolds] using this
      have hpured : (p.1, h_b) ∈ pureDen Hd0.2.1 := fun a ha' =>
        hatoms a (by
          change a ∈ [(true, (sig.get j).1, (sig'.get k).1),
            (true, (sig.get j).2, (sig'.get k).2)] ++ Hd0.2.1
          exact List.mem_append.mpr (Or.inr ha'))
      have hshd0 : (p.1, h_b) ∈ shDen Hd0 := by
        simpa [shDen, qfDen, hb0] using And.intro hpured hbody
      have hdisjD : (p.1, h_b) ∈ disjDen (Ds j) := ⟨Hd0, hmem0, hshd0⟩
      obtain ⟨v, w, huvw, hv, hw⟩ := spatialDen_split sig p.1 h_a j hsa
      obtain ⟨hcuvw, hdvw⟩ := isUnion_iff.1 huvw
      have hdab' : Heap.Disjoint (union v w) h_b := by
        rw [hcuvw] at hdab
        exact hdab
      have hv_hb : Heap.Disjoint v h_b := disjoint_of_union_left hdab'
      have hw_hb : Heap.Disjoint w h_b := disjoint_of_union_right hdab'
      have hmem : (p.1, union w h_b) ∈ sepConj (lhsDen (pi, sig.eraseIdx j)) (disjDen (Ds j)) := by
        refine Exists.intro w (Exists.intro h_b ?_)
        exact ⟨isUnion_union hw_hb, ⟨hpa, hw⟩, hdisjD⟩
      have hIH := ihj j conv_nil hmem
      obtain ⟨hpur', hspat'⟩ := hIH
      have hv' : (p.1, v) ∈ ptsDen (sig'.get k) := ptsDen_of_eval_eq heq1 heq2 hv
      have huIns : Heap.IsUnion p.2 v (union w h_b) :=
        isUnion_iff.2 ⟨by rw [hcab, hcuvw, union_assoc], disjoint_union_right hdvw hv_hb⟩
      refine ⟨pureDen_snd hpur', ?_⟩
      exact spatialDen_insert_of_isUnion hv' hspat' huIns
    · -- second disjunct: `D ∗ L'_k ↦ R'_k`
      obtain ⟨Hd0, hmem0, rfl⟩ := List.mem_map.1 hmem
      have hb0 : Hd0.1 = [] := binders_empty hd rfl Hd0 hmem0
      have hbq : (p.1, h_b) ∈ qfDen (Hd0.2.1, sig'.get k :: Hd0.2.2.1, Hd0.2.2.2) := by
        simpa [shDen, addPts, hb0] using hbden
      obtain ⟨hpure0, hspat0⟩ := hbq
      obtain ⟨c, hb', huc, hc, hb'den⟩ := hspat0
      obtain ⟨hcb, hdchb'⟩ := isUnion_iff.1 huc
      have hcb' : h_b = union c hb' := hcb
      have hb'qf : (p.1, hb') ∈ shDen Hd0 := by
        have h1 : (p.1, hb') ∈ pureDen Hd0.2.1 := pureDen_snd hpure0
        rw [shDen, hb0]
        exact ⟨h1, hb'den⟩
      have hdisjD : (p.1, hb') ∈ disjDen D := ⟨Hd0, hmem0, hb'qf⟩
      have hd_a_c : Heap.Disjoint h_a c := (disjoint_of_isUnion_right hdab huc).1
      have hd_a_b' : Heap.Disjoint h_a hb' := (disjoint_of_isUnion_right hdab huc).2
      have hmem : (p.1, union h_a hb') ∈ sepConj (lhsDen (pi, sig)) (disjDen D) := by
        refine Exists.intro h_a (Exists.intro hb' ?_)
        exact ⟨isUnion_union hd_a_b', ⟨hpa, hsa⟩, hdisjD⟩
      have hIH := ihd conv_nil hmem
      obtain ⟨hpur', hspat'⟩ := hIH
      have huIns : Heap.IsUnion p.2 c (union h_a hb') :=
        isUnion_iff.2 ⟨by rw [hcab, hcb', union_rotate hd_a_c hd_a_b' hdchb'],
          disjoint_union_right (disjoint_comm hd_a_c) hdchb'⟩
      refine ⟨pureDen_snd hpur', ?_⟩
      exact spatialDen_insert_of_isUnion hc hspat' huIns
  | exists_r Δ D q X h ih =>
    intro hconv p hp
    obtain ⟨h_a, h_b, hu, ha, hb⟩ := hp
    obtain ⟨hcab, hdab⟩ := isUnion_iff.1 hu
    rcases hb with ⟨Hd, hmem, hbden⟩
    obtain ⟨Hd0, hmem0, rfl⟩ := List.mem_map.1 hmem
    have hb0 : Hd0.1 = [] := binders_empty h rfl Hd0 hmem0
    have hbX : (p.1, h_b) ∈ X.foldr exQ (qfDen Hd0.2) := by
      rw [shDen, bindVars] at hbden
      rw [hb0, List.append_nil] at hbden
      exact hbden
    obtain ⟨s', hs', hb'⟩ := mem_foldr_exQ_of_mem hbX
    have hb'qf : (s', h_b) ∈ shDen Hd0 := by
      simpa [shDen, hb0] using hb'
    have hdisjD : (s', h_b) ∈ disjDen D := ⟨Hd0, hmem0, hb'qf⟩
    have ha' : (s', h_a) ∈ lhsDen Δ := by
      refine lhsDen_congr (s := p.1) ?_ ha
      intro x hx
      exact hs' x (fun hc => hconv x hc hx)
    have hmem : (s', union h_a h_b) ∈ sepConj (lhsDen Δ) (disjDen D) := by
      refine Exists.intro h_a (Exists.intro h_b ?_)
      exact ⟨isUnion_union hdab, ha', hdisjD⟩
    have hIH := ih conv_nil hmem
    have hp : p = (p.1, union h_a h_b) := by
      obtain ⟨s, h⟩ := p
      simpa using hcab
    rw [hp]
    refine mem_foldr_exQ_qf (q := q) (X := X) (s := p.1) (s' := s') ?_ ?_
    · intro x _ hxX
      exact hs' x hxX
    · exact hIH

end Soundness89

/-- **§3.4.2 (p. 28).** The rules of Figure 2 derive solutions of the abduction question (5):
from `Δ ∗ [D] ▷ H` it follows that `D` is a solution of `Δ` for `H`. -/
theorem solution (Δ : LHS) (D : Disj) (H : SH) (hconv : Conv Δ H) (hder : Derives Δ D H) :
    IsSolution (lhsDen Δ) (shDen H) (disjDen D) :=
  Soundness89.solution Δ D H hconv hder

#print axioms solution
