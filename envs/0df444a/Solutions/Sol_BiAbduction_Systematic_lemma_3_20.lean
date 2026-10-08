-- Prove2me | solution 1 for BiAbduction.Systematic.lemma_3_20
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T11:08:26.379048+00:00
-- url     : https://prove2.me/submissions/a4bb9c9a-4316-4366-a9cb-57c8365d0a81

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Incompat

open BiAbduction.Systematic

/-!
Lemma 3.20 (p. 32): `Incompat(Δ)` and `¬ Elsewhere(Δ)` denote the same states.

`Elsewhere(Δ) = ¬(Δ −∗ false)` says that *some* separate heap satisfies `Δ`; so
`¬ Elsewhere(Δ)` says that no heap disjoint from the current one satisfies `Δ`.  Since `Δ` fixes
the heap completely (`Δ.2` is a `∗`-conjunction of points-to facts ending in `emp`), this happens
exactly when one of the four syntactic conditions of `Incompat(Δ)` holds: some pure atom fails,
some location expression is nil, two location expressions coincide, or some location of `Δ` is
already allocated in the current heap.
-/

namespace Incompat20

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

theorem disjoint_union {h₀ h₁ h₂ : Heap} (h₀₂ : Heap.Disjoint h₀ h₂) (h₁₂ : Heap.Disjoint h₁ h₂) :
    Heap.Disjoint (union h₀ h₁) h₂ := by
  intro l
  rcases h₀₂ l with h | h
  · rcases h₁₂ l with h' | h'
    · left
      change (h₀.cell l).or (h₁.cell l) = none
      rw [h, h']
      rfl
    · exact Or.inr h'
  · exact Or.inr h

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

/-! ## Semantic lemmas -/

theorem spatialDen_cons (pt : PtsTo) (sig : List PtsTo) (tr : Bool) :
    spatialDen (pt :: sig) tr = sepConj (ptsDen pt) (spatialDen sig tr) := rfl

theorem get_cons_zero' (a : PtsTo) (rest : List PtsTo) :
    (a :: rest).get (0 : Fin (a :: rest).length) = a := List.get_cons_zero ..

theorem get_cons_succ' {a : PtsTo} {rest : List PtsTo} (k : Fin rest.length) :
    (a :: rest).get k.succ = rest.get k := List.get_cons_succ ..

/-- The cell prescribed by the `k`-th points-to fact is the one the heap carries. -/
theorem spatialDen_cell_aux : ∀ (sig : List PtsTo) (tr : Bool) (s : Stack) (h : Heap)
    (k : Fin sig.length), (s, h) ∈ spatialDen sig tr →
      h.cell (evalE s (sig.get k).1) = some (evalE s (sig.get k).2) := by
  intro sig
  induction sig with
  | nil => intro tr s h k hh; exact absurd k.isLt (Nat.not_lt_zero k.1)
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

theorem spatialDen_cell {s : Stack} {h : Heap} {sig : List PtsTo} {tr : Bool}
    (hh : (s, h) ∈ spatialDen sig tr) (k : Fin sig.length) :
    h.cell (evalE s (sig.get k).1) = some (evalE s (sig.get k).2) :=
  spatialDen_cell_aux sig tr s h k hh

/-- Distinct positions of a points-to list denote distinct locations. -/
theorem spatialDen_inj_aux : ∀ (sig : List PtsTo) (tr : Bool) (s : Stack) (h : Heap)
    (i j : Fin sig.length), (s, h) ∈ spatialDen sig tr →
      evalE s (sig.get i).1 = evalE s (sig.get j).1 → i = j := by
  intro sig
  induction sig with
  | nil => intro tr s h i j hh _; exact absurd i.isLt (Nat.not_lt_zero i.1)
  | cons a rest ih =>
    intro tr s h i j hh hij
    rw [spatialDen_cons] at hh
    obtain ⟨h₀, h₁, hu, h0, h1⟩ := hh
    obtain ⟨hd, hc⟩ := hu
    have h0' : h₀.cell (evalE s a.1) = some (evalE s a.2) := by
      have h2 := h0
      simp only [ptsDen, Set.mem_setOf_eq] at h2
      simpa using h2.2 (evalE s a.1)
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j' =>
        exfalso
        rw [get_cons_zero', get_cons_succ'] at hij
        have hcell := spatialDen_cell h1 j'
        rw [← hij] at hcell
        rcases hd (evalE s a.1) with hd0 | hd1
        · rw [h0'] at hd0
          exact absurd hd0 (by simp)
        · rw [hcell] at hd1
          exact absurd hd1 (by simp)
    | succ i' =>
      cases j using Fin.cases with
      | zero =>
        exfalso
        rw [get_cons_zero', get_cons_succ'] at hij
        have hcell := spatialDen_cell h1 i'
        rw [hij] at hcell
        rcases hd (evalE s a.1) with hd0 | hd1
        · rw [h0'] at hd0
          exact absurd hd0 (by simp)
        · rw [hcell] at hd1
          exact absurd hd1 (by simp)
      | succ j' =>
        rw [get_cons_succ'] at hij
        exact Fin.succ_inj.mpr (ih tr s h₁ i' j' h1 hij)

theorem spatialDen_inj {s : Stack} {h : Heap} {sig : List PtsTo} {tr : Bool}
    (hh : (s, h) ∈ spatialDen sig tr) (i j : Fin sig.length)
    (hij : evalE s (sig.get i).1 = evalE s (sig.get j).1) : i = j :=
  spatialDen_inj_aux sig tr s h i j hh hij

/-- The heap `[[[L₁]]↦[[R₁]], …, [[Lₙ]]↦[[Rₙ]]]`. -/
def mkHeap (s : Stack) : List PtsTo → Heap
  | [] => emptyHeap
  | pt :: rest => union (ptsHeap (evalE s pt.1) (evalE s pt.2)) (mkHeap s rest)

/-- `mkHeap` satisfies `Σ` as soon as the locations are nonzero and pairwise distinct. -/
theorem mkHeap_spec (s : Stack) (sig : List PtsTo)
    (hne : ∀ k : Fin sig.length, evalE s (sig.get k).1 ≠ 0)
    (hinj : ∀ i j : Fin sig.length, i ≠ j → evalE s (sig.get i).1 ≠ evalE s (sig.get j).1) :
    (s, mkHeap s sig) ∈ spatialDen sig false ∧
      (∀ k : Fin sig.length,
        (mkHeap s sig).cell (evalE s (sig.get k).1) = some (evalE s (sig.get k).2)) ∧
      (∀ l, (∀ k : Fin sig.length, evalE s (sig.get k).1 ≠ l) →
        (mkHeap s sig).cell l = none) := by
  induction sig with
  | nil =>
    refine ⟨?_, ?_, ?_⟩
    · show (s, emptyHeap) ∈ emp
      intro l
      rfl
    · intro k
      exact absurd k.isLt (Nat.not_lt_zero k.1)
    · intro l _
      rfl
  | cons a rest ih =>
    have hne' : ∀ k : Fin rest.length, evalE s (rest.get k).1 ≠ 0 := by
      intro k
      have h := hne k.succ
      simpa using h
    have hinj' : ∀ i j : Fin rest.length, i ≠ j →
        evalE s (rest.get i).1 ≠ evalE s (rest.get j).1 := by
      intro i j hij
      have h := hinj i.succ j.succ (fun hc => hij (Fin.succ_inj.mp hc))
      simpa using h
    obtain ⟨ih1, ih2, ih3⟩ := ih hne' hinj'
    have ha0 : evalE s a.1 ≠ 0 := by
      have h := hne 0
      simpa using h
    have hcons : ∀ k : Fin rest.length, evalE s (rest.get k).1 ≠ evalE s a.1 := by
      intro k
      have h := hinj 0 k.succ (Fin.succ_ne_zero k).symm
      rw [get_cons_zero', get_cons_succ'] at h
      exact h.symm
    refine ⟨?_, ?_, ?_⟩
    · rw [spatialDen_cons]
      refine ⟨ptsHeap (evalE s a.1) (evalE s a.2), mkHeap s rest, ?_, ?_, ih1⟩
      · refine isUnion_iff.2 ⟨rfl, ?_⟩
        intro l
        by_cases hl : l = evalE s a.1
        · right
          refine ih3 l ?_
          intro k
          rw [hl]
          exact hcons k
        · left
          simp [ptsHeap, hl]
      · refine ⟨ha0, ?_⟩
        intro l
        by_cases hl : l = evalE s a.1
        · subst hl
          simp [ptsHeap, ha0]
        · simp [ptsHeap, hl]
    · intro k
      cases k using Fin.cases with
      | zero =>
        rw [get_cons_zero']
        have hM : (mkHeap s rest).cell (evalE s a.1) = none := by
          refine ih3 _ ?_
          intro j
          exact hcons j
        change (union (ptsHeap (evalE s a.1) (evalE s a.2)) (mkHeap s rest)).cell
          (evalE s a.1) = some (evalE s a.2)
        rw [union_cell, hM, or_none_eq]
        exact ptsHeap_cell_self _ _ ha0
      | succ i =>
        rw [get_cons_succ']
        have hP : (ptsHeap (evalE s a.1) (evalE s a.2)).cell
            (evalE s (rest.get i).1) = none := by
          have hne_i : evalE s (rest.get i).1 ≠ evalE s a.1 := hcons i
          exact ptsHeap_cell_of_ne hne_i
        change (union (ptsHeap (evalE s a.1) (evalE s a.2)) (mkHeap s rest)).cell
          (evalE s (rest.get i).1) = some (evalE s (rest.get i).2)
        rw [union_cell, hP]
        simpa using ih2 i
    · intro l hl
      change (union (ptsHeap (evalE s a.1) (evalE s a.2)) (mkHeap s rest)).cell l = none
      rw [union_cell]
      have hP : (ptsHeap (evalE s a.1) (evalE s a.2)).cell l = none := by
        have h0 := hl 0
        rw [get_cons_zero'] at h0
        exact ptsHeap_cell_of_ne h0.symm
      have hM : (mkHeap s rest).cell l = none := by
        refine ih3 l ?_
        intro k
        have h := hl k.succ
        rw [get_cons_succ'] at h
        exact h
      rw [hP, hM]
      rfl

/-! ## Freshness and evaluation -/

theorem le_foldr_max (l : List ℕ) (x : ℕ) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => exact absurd hx (by simp)
  | cons a t ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih hx) (le_max_right _ _)

theorem freshVar_ne {Δ : LHS} {x : ℕ} (hx : x ∈ lhsVars Δ) : x ≠ freshVar Δ := by
  have h1 : x ≤ (lhsVars Δ).foldr max 0 := le_foldr_max _ x hx
  simp only [freshVar]
  omega

/-- `freshVar Δ` does not occur in the left-hand side, so evaluating heads of its points-to facts
is independent of the value of `freshVar Δ`. -/
theorem evalE_update_fresh {Δ : LHS} {pt : PtsTo} (hpt : pt ∈ Δ.2) (s : Stack) (v : ℕ) :
    evalE (Function.update s (freshVar Δ) v) pt.1 = evalE s pt.1 := by
  rcases pt with ⟨e, e'⟩
  have hx : ∀ x : ℕ, e = Sum.inl x → x ≠ freshVar Δ := by
    intro x hx
    refine freshVar_ne ?_
    rw [lhsVars]
    refine List.mem_append.mpr (Or.inr ?_)
    refine List.mem_flatMap.mpr ⟨(e, e'), hpt, ?_⟩
    rw [hx]
    simp [exprVars]
  cases e with
  | inl x =>
    simp only [evalE]
    exact Function.update_of_ne (hx x rfl) v s
  | inr k => rfl

theorem atomHolds_negAtom (s : Stack) (a : PureAtom) :
    atomHolds s (negAtom a) ↔ ¬ atomHolds s a := by
  rcases a with ⟨f, e, e'⟩
  cases f <;> simp [atomHolds, negAtom]

/-! ## Lemma 3.20 -/

theorem solution_aux (Δ : LHS) : disjDen (incompat Δ) = (Elsewhere (lhsDen Δ))ᶜ := by
  rw [Elsewhere, compl_compl]
  ext p
  constructor
  · -- a state of `Incompat(Δ)` admits no separate heap satisfying `Δ`
    rintro hp h' hu hisU hΔ
    exfalso
    have hΔ' : (p.1, h') ∈ pureDen Δ.1 ∧ (p.1, h') ∈ spatialDen Δ.2 false := by
      have h := hΔ
      simp only [lhsDen, qfDen, Set.mem_inter_iff] at h
      exact h
    obtain ⟨hAtoms, hSpat⟩ := hΔ'
    obtain ⟨H, hH, hpH⟩ := hp
    obtain ⟨hdU, -⟩ := hisU
    simp only [incompat] at hH
    rw [List.mem_append] at hH
    rcases hH with hH | hH
    · rw [List.mem_append] at hH
      rcases hH with hH | hH
      · rw [List.mem_append] at hH
        rcases hH with hH | hH
        · -- some pure atom of `Δ` fails
          rcases List.mem_map.mp hH with ⟨a, ha, rfl⟩
          have hpa : atomHolds p.1 (negAtom a) := by
            have h1 := hpH
            simp only [shDen, List.foldr_nil, qfDen, pureDen, Set.mem_inter_iff,
              Set.mem_setOf_eq] at h1
            simpa using h1.1
          exact (atomHolds_negAtom p.1 a).mp hpa (hAtoms a ha)
        · -- some location expression of `Δ` is nil
          rcases List.mem_map.mp hH with ⟨pt, hpt, rfl⟩
          have hpt0 : evalE p.1 pt.1 = 0 := by
            have h1 := hpH
            simp only [shDen, List.foldr_nil, qfDen, pureDen, Set.mem_inter_iff,
              Set.mem_setOf_eq] at h1
            have h2 : atomHolds p.1 (true, pt.1, Sum.inr 0) := by simpa using h1.1
            simpa [atomHolds, evalE] using h2
          rcases List.mem_iff_get.mp hpt with ⟨k, hk⟩
          have hc := spatialDen_cell hSpat k
          rw [hk] at hc
          rw [hpt0] at hc
          exact absurd hc (by simp [h'.nil_unalloc])
      · -- two location expressions of `Δ` coincide
        rcases List.mem_flatMap.mp hH with ⟨i, -, hH⟩
        rcases List.mem_flatMap.mp hH with ⟨j, -, hH⟩
        by_cases hij : i = j
        · simp [hij] at hH
        · rcases List.mem_singleton.mp (by simpa [hij] using hH) with rfl
          have hij' : evalE p.1 (Δ.2.get i).1 = evalE p.1 (Δ.2.get j).1 := by
            have h1 := hpH
            simp only [shDen, List.foldr_nil, qfDen, pureDen, Set.mem_inter_iff,
              Set.mem_setOf_eq] at h1
            have h2 : atomHolds p.1 (true, (Δ.2.get i).1, (Δ.2.get j).1) := by simpa using h1.1
            simpa [atomHolds, evalE] using h2
          exact hij (spatialDen_inj hSpat i j hij')
    · -- some location of `Δ` is already allocated
      rcases List.mem_map.mp hH with ⟨pt, hpt, rfl⟩
      have hsh : p ∈ shDen ([freshVar Δ], ([], [(pt.1, Sum.inl (freshVar Δ))], true)) := hpH
      simp only [shDen, exQ, List.foldr_cons, List.foldr_nil] at hsh
      obtain ⟨v, hv⟩ := hsh
      obtain ⟨-, hv⟩ := hv
      rw [spatialDen_cons] at hv
      obtain ⟨h₀, h₁, hu₀, h0, -⟩ := hv
      obtain ⟨hd₀, hc₀⟩ := hu₀
      have hcell : h₀.cell (evalE (Function.update p.1 (freshVar Δ) v) pt.1) = some v := by
        have h2 := h0
        simp only [ptsDen, Set.mem_setOf_eq] at h2
        have h3 := h2.2 (evalE (Function.update p.1 (freshVar Δ) v) pt.1)
        simpa [evalE, Function.update_self] using h3
      have hupd : evalE (Function.update p.1 (freshVar Δ) v) pt.1 = evalE p.1 pt.1 :=
        evalE_update_fresh (Δ := Δ) hpt p.1 v
      have hp2 : p.2.cell (evalE p.1 pt.1) = some v := by
        rw [← hupd]
        rw [hc₀ (evalE (Function.update p.1 (freshVar Δ) v) pt.1)]
        rw [hcell]
        rfl
      rcases List.mem_iff_get.mp hpt with ⟨k, hk⟩
      have hc := spatialDen_cell hSpat k
      rw [hk] at hc
      rcases hdU (evalE p.1 pt.1) with hz | hz
      · rw [hp2] at hz
        exact absurd hz (by simp)
      · rw [hc] at hz
        exact absurd hz (by simp)
  · -- a state with no separate extension is a state of `Incompat(Δ)`
    intro hno
    by_cases hA : ∃ a ∈ Δ.1, ¬ atomHolds p.1 a
    · rcases hA with ⟨a, ha, hna⟩
      refine ⟨([], ([negAtom a], [], true)), ?_, ?_⟩
      · exact List.mem_append.mpr
          (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
            (Or.inl (List.mem_map.mpr ⟨a, ha, rfl⟩))))))
      · show p ∈ qfDen ([negAtom a], [], true)
        refine ⟨?_, trivial⟩
        intro b hb
        simp only [List.mem_singleton] at hb
        subst hb
        exact (atomHolds_negAtom p.1 a).mpr hna
    · by_cases hB : ∃ k : Fin Δ.2.length, evalE p.1 (Δ.2.get k).1 = 0
      · rcases hB with ⟨k, hk⟩
        refine ⟨([], ([(true, (Δ.2.get k).1, Sum.inr 0)], [], true)), ?_, ?_⟩
        · exact List.mem_append.mpr
            (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
              (Or.inr (List.mem_map.mpr ⟨Δ.2.get k, List.get_mem Δ.2 k, rfl⟩))))))
        · show p ∈ qfDen ([(true, (Δ.2.get k).1, Sum.inr 0)], [], true)
          refine ⟨?_, trivial⟩
          intro b hb
          simp only [List.mem_singleton] at hb
          subst hb
          simpa [atomHolds, evalE] using hk
      · by_cases hC : ∃ i j : Fin Δ.2.length,
            i ≠ j ∧ evalE p.1 (Δ.2.get i).1 = evalE p.1 (Δ.2.get j).1
        · rcases hC with ⟨i, j, hij, hLij⟩
          refine ⟨([], ([(true, (Δ.2.get i).1, (Δ.2.get j).1)], [], true)), ?_, ?_⟩
          · refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_)))
            refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩
            refine List.mem_flatMap.mpr ⟨j, List.mem_finRange j, ?_⟩
            simpa [hij] using (List.mem_singleton.mpr rfl :
              ([], ([(true, (Δ.2.get i).1, (Δ.2.get j).1)], [], true)) ∈
                [([], ([(true, (Δ.2.get i).1, (Δ.2.get j).1)], [], true))])
          · show p ∈ qfDen ([(true, (Δ.2.get i).1, (Δ.2.get j).1)], [], true)
            refine ⟨?_, trivial⟩
            intro b hb
            simp only [List.mem_singleton] at hb
            subst hb
            simpa [atomHolds] using hLij
        · by_cases hD : ∃ (k : Fin Δ.2.length) (v : ℕ),
              p.2.cell (evalE p.1 (Δ.2.get k).1) = some v
          · rcases hD with ⟨k, v, hv⟩
            refine ⟨([freshVar Δ], ([], [((Δ.2.get k).1, Sum.inl (freshVar Δ))], true)), ?_, ?_⟩
            · exact List.mem_append.mpr
                (Or.inr (List.mem_map.mpr ⟨Δ.2.get k, List.get_mem Δ.2 k, rfl⟩))
            · show p ∈ shDen ([freshVar Δ], ([], [((Δ.2.get k).1, Sum.inl (freshVar Δ))], true))
              refine ⟨v, ?_⟩
              show (Function.update p.1 (freshVar Δ) v, p.2) ∈
                qfDen ([], [((Δ.2.get k).1, Sum.inl (freshVar Δ))], true)
              refine ⟨?_, ?_⟩
              · intro b hb
                simp at hb
              · rw [spatialDen_cons]
                refine ⟨ptsHeap (evalE (Function.update p.1 (freshVar Δ) v) (Δ.2.get k).1) v,
                  eraseCell p.2 (evalE (Function.update p.1 (freshVar Δ) v) (Δ.2.get k).1),
                  ?_, ?_, trivial⟩
                · refine isUnion_eraseCell ?_
                  rw [evalE_update_fresh (Δ := Δ) (List.get_mem Δ.2 k) p.1 v]
                  exact hv
                · refine ⟨?_, ?_⟩
                  · rw [evalE_update_fresh (Δ := Δ) (List.get_mem Δ.2 k) p.1 v]
                    exact fun h0 => hB ⟨k, h0⟩
                  · intro l'
                    by_cases hl' : l' = evalE (Function.update p.1 (freshVar Δ) v) (Δ.2.get k).1
                    · have hl0 : evalE (Function.update p.1 (freshVar Δ) v) (Δ.2.get k).1 ≠ 0 := by
                        rw [evalE_update_fresh (Δ := Δ) (List.get_mem Δ.2 k) p.1 v]
                        exact fun h0 => hB ⟨k, h0⟩
                      rw [hl', ptsHeap_cell_self _ _ hl0]
                      simp [evalE, Function.update_self]
                    · rw [ptsHeap_cell_of_ne hl', if_neg hl']
          · exfalso
            have hAtoms : ∀ a ∈ Δ.1, atomHolds p.1 a := by
              intro a ha
              by_contra hna
              exact hA ⟨a, ha, hna⟩
            have hne' : ∀ k : Fin Δ.2.length, evalE p.1 (Δ.2.get k).1 ≠ 0 := by
              intro k hk
              exact hB ⟨k, hk⟩
            have hinj' : ∀ i j : Fin Δ.2.length, i ≠ j →
                evalE p.1 (Δ.2.get i).1 ≠ evalE p.1 (Δ.2.get j).1 := by
              intro i j hij h
              exact hC ⟨i, j, hij, h⟩
            have hnD : ∀ (k : Fin Δ.2.length) (v : ℕ),
                p.2.cell (evalE p.1 (Δ.2.get k).1) ≠ some v := by
              intro k v hv
              exact hD ⟨k, v, hv⟩
            obtain ⟨hsp, -, hnone⟩ := mkHeap_spec p.1 Δ.2 hne' hinj'
            refine hno (mkHeap p.1 Δ.2) (union p.2 (mkHeap p.1 Δ.2)) ?_ ?_
            · refine isUnion_union ?_
              intro l
              by_cases hl : ∃ k : Fin Δ.2.length, evalE p.1 (Δ.2.get k).1 = l
              · rcases hl with ⟨k, hk⟩
                left
                rw [← hk]
                cases hcell : p.2.cell (evalE p.1 (Δ.2.get k).1) with
                | none => rfl
                | some v => exact absurd hcell (hnD k v)
              · right
                refine hnone l ?_
                intro k hk
                exact hl ⟨k, hk⟩
            · show (p.1, mkHeap p.1 Δ.2) ∈ pureDen Δ.1 ∩ spatialDen Δ.2 false
              exact ⟨hAtoms, hsp⟩

end Incompat20

/-- **Lemma 3.20.** `Incompat(Δ)` and `¬ Elsewhere(Δ)` denote the same states. -/
theorem solution (Δ : LHS) : disjDen (incompat Δ) = (Elsewhere (lhsDen Δ))ᶜ :=
  Incompat20.solution_aux Δ

#print axioms solution
