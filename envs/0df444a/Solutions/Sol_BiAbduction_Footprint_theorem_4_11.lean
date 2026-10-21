-- Prove2me | solution 1 for BiAbduction.Footprint.theorem_4_11
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T22:12:34.017121+00:00
-- url     : https://prove2.me/submissions/ee3a90ff-7111-49f0-95ff-859702838275

import Mathlib
import Definitions.Def_BiAbduction_Footprint_Semantics
import Definitions.Def_BiAbduction_Footprint_Footprint

open BiAbduction.Footprint

open BiAbduction.Footprint

namespace FootprintProof

@[ext] theorem heap_ext {a b : Heap} (h : ∀ l, a.cell l = b.cell l) : a = b := by
  cases a
  cases b
  congr
  funext l
  exact h l

theorem sub_refl (a : Heap) : Heap.Subheap a a := by intro l v h; exact h

theorem sub_trans {a b c : Heap} (hab : Heap.Subheap a b) (hbc : Heap.Subheap b c) :
    Heap.Subheap a c := by intro l v h; exact hbc l v (hab l v h)

theorem sub_antisymm {a b : Heap} (hab : Heap.Subheap a b) (hba : Heap.Subheap b a) :
    a = b := by
  apply heap_ext
  intro l
  cases ha : a.cell l with
  | none =>
    cases hb : b.cell l with
    | none => rfl
    | some v => have := hba l v hb; simp [ha] at this
  | some v => exact (hab l v ha).symm

def emptyHeap : Heap where
  cell := fun _ => none
  nil_unalloc := rfl
  finite_dom := by simp

def join (a b : Heap) : Heap where
  cell := fun l => (a.cell l).or (b.cell l)
  nil_unalloc := by simp [a.nil_unalloc, b.nil_unalloc]
  finite_dom := (a.finite_dom.union b.finite_dom).subset (by
    intro l h
    by_cases ha : a.cell l = none
    · right; simpa [ha] using h
    · exact Or.inl ha)

theorem union_comm {h a b : Heap} (hu : Heap.IsUnion h a b) : Heap.IsUnion h b a := by
  constructor
  · intro l; exact (hu.1 l).symm
  · intro l
    rw [hu.2 l]
    rcases hu.1 l with ha | hb
    · simp [ha]
    · simp [hb]

theorem join_union {a b : Heap} (hd : Heap.Disjoint a b) : Heap.IsUnion (join a b) a b :=
  ⟨hd, fun _ => rfl⟩

theorem union_sub_left {h a b : Heap} (hu : Heap.IsUnion h a b) : Heap.Subheap a h := by
  intro l v hv
  rw [hu.2 l, hv]
  rfl

theorem union_sub_right {h a b : Heap} (hu : Heap.IsUnion h a b) : Heap.Subheap b h :=
  union_sub_left (union_comm hu)

theorem disjoint_of_sub_left {a a' b : Heap} (hd : Heap.Disjoint a b)
    (hs : Heap.Subheap a' a) : Heap.Disjoint a' b := by
  intro l
  rcases hd l with ha | hb
  · left
    cases hx : a'.cell l with
    | none => rfl
    | some v => have := hs l v hx; simp [ha] at this
  · exact Or.inr hb

theorem disjoint_of_sub_right {a b b' : Heap} (hd : Heap.Disjoint a b)
    (hs : Heap.Subheap b' b) : Heap.Disjoint a b' := by
  intro l
  exact (disjoint_of_sub_left (fun l => (hd l).symm) hs l).symm

theorem join_sub_union {h a b a' b' : Heap} (hu : Heap.IsUnion h a b)
    (ha : Heap.Subheap a' a) (hb : Heap.Subheap b' b) : Heap.Subheap (join a' b') h := by
  intro l v hv
  change (a'.cell l).or (b'.cell l) = some v at hv
  cases hx : a'.cell l with
  | none => exact union_sub_right hu l v (hb l v (by simpa [hx] using hv))
  | some w =>
    have hw : w = v := by simpa [hx] using hv
    subst w
    exact union_sub_left hu l v (ha l v hx)

theorem union_mono_left {h a b a' : Heap} (hu : Heap.IsUnion h a b)
    (ha : Heap.Subheap a' a) : ∃ h', Heap.IsUnion h' a' b ∧ Heap.Subheap h' h :=
  ⟨join a' b, join_union (disjoint_of_sub_left hu.1 ha), join_sub_union hu ha (sub_refl b)⟩

theorem union_mono_right {h a b b' : Heap} (hu : Heap.IsUnion h a b)
    (hb : Heap.Subheap b' b) : ∃ h', Heap.IsUnion h' a b' ∧ Heap.Subheap h' h :=
  ⟨join a b', join_union (disjoint_of_sub_right hu.1 hb), join_sub_union hu (sub_refl a) hb⟩

theorem union_cancel_left {h h' a b b' : Heap} (hu : Heap.IsUnion h a b)
    (hu' : Heap.IsUnion h' a b') (hh : Heap.Subheap h h') : Heap.Subheap b b' := by
  intro l v hv
  have ha : a.cell l = none := (hu.1 l).resolve_right (by simp [hv])
  have hhv : h.cell l = some v := by rw [hu.2 l]; simp [ha, hv]
  have hhv' := hh l v hhv
  rw [hu'.2 l] at hhv'
  simpa [ha] using hhv'

theorem union_ext {h h' a b : Heap} (hu : Heap.IsUnion h a b)
    (hu' : Heap.IsUnion h' a b) : h = h' :=
  heap_ext (fun l => (hu.2 l).trans (hu'.2 l).symm)

noncomputable def remainder (h a : Heap) : Heap where
  cell := fun l => if a.cell l = none then h.cell l else none
  nil_unalloc := by simp [h.nil_unalloc]
  finite_dom := h.finite_dom.subset (by
    intro l hl
    by_cases ha : a.cell l = none <;> simp_all)

theorem sub_split {a h : Heap} (hs : Heap.Subheap a h) :
    ∃ b, Heap.IsUnion h a b := by
  classical
  refine ⟨remainder h a, ?_, ?_⟩
  · intro l
    by_cases ha : a.cell l = none
    · exact Or.inl ha
    · exact Or.inr (by simp [remainder, ha])
  · intro l
    cases ha : a.cell l with
    | none => simp [remainder, ha]
    | some v => simp [remainder, ha, hs l v ha]

theorem empty_sub (a : Heap) : Heap.Subheap emptyHeap a := by
  intro l v h
  simp [emptyHeap] at h

theorem union_empty_right (a : Heap) : Heap.IsUnion a a emptyHeap := by
  constructor
  · intro l; exact Or.inr rfl
  · intro l; simp [emptyHeap]

end FootprintProof

open BiAbduction.Footprint

namespace FootprintProof

noncomputable def domain (h : Heap) : Finset ℕ := h.finite_dom.toFinset

@[simp] theorem mem_domain (h : Heap) (l : ℕ) : l ∈ domain h ↔ h.cell l ≠ none := by
  simp [domain]

theorem domain_mono {a b : Heap} (hs : Heap.Subheap a b) : domain a ⊆ domain b := by
  intro l hl
  rw [mem_domain] at hl ⊢
  cases ha : a.cell l with
  | none => exact (hl ha).elim
  | some v => simp [hs l v ha]

theorem sub_eq_of_card_le {a b : Heap} (hs : Heap.Subheap a b)
    (hc : (domain b).card ≤ (domain a).card) : a = b := by
  have hd : domain a = domain b := Finset.eq_of_subset_of_card_le (domain_mono hs) hc
  apply heap_ext
  intro l
  cases ha : a.cell l with
  | some v => exact (hs l v ha).symm
  | none =>
    have hn : l ∉ domain b := by rw [← hd]; simp [ha]
    have hb : b.cell l = none := by simpa using hn
    exact hb.symm

theorem minSet_subset (F : Pred) : minSet F ⊆ F := by
  intro p hp
  exact hp.1

theorem exists_min_subheap {F : Pred} {s : Stack} {h : Heap} (hf : (s, h) ∈ F) :
    ∃ a : Heap, Heap.Subheap a h ∧ (s, a) ∈ minSet F := by
  classical
  have hex : ∃ n : ℕ, ∃ a : Heap, Heap.Subheap a h ∧ (s, a) ∈ F ∧ (domain a).card = n :=
    ⟨(domain h).card, h, sub_refl h, hf, rfl⟩
  obtain ⟨a, ha, hfa, hcard⟩ := Nat.find_spec hex
  refine ⟨a, ha, hfa, ?_⟩
  intro b hba hfb
  apply sub_eq_of_card_le hba
  rw [hcard]
  exact Nat.find_min' hex ⟨b, sub_trans hba ha, hfb, rfl⟩

theorem upward_mem_iff (F : Pred) (s : Stack) (h : Heap) :
    (s, h) ∈ sepConj F Set.univ ↔ ∃ a : Heap, Heap.Subheap a h ∧ (s, a) ∈ F := by
  constructor
  · rintro ⟨a, b, hu, hf, _⟩
    exact ⟨a, union_sub_left hu, hf⟩
  · rintro ⟨a, ha, hf⟩
    obtain ⟨b, hu⟩ := sub_split ha
    exact ⟨a, b, hu, hf, Set.mem_univ _⟩

theorem solution_iff_subset_wand (F G M : Pred) :
    IsSolution F G M ↔ M ⊆ wand F G := by
  constructor
  · intro hs p hp a u hu hfa
    exact hs ⟨a, p.2, union_comm hu, hfa, hp⟩
  · intro hw p hp
    obtain ⟨a, b, hu, hfa, hmb⟩ := hp
    exact hw hmb a p.2 (union_comm hu) hfa

theorem least_solution_eq {F G M : Pred} (hleast : IsLeastSolution F G M) :
    M = minSet (wand F G) := by
  have hm : M ⊆ wand F G := (solution_iff_subset_wand F G M).mp hleast.1
  have hk : IsSolution F G (minSet (wand F G)) :=
    (solution_iff_subset_wand F G _).mpr (minSet_subset _)
  have hkm : SpatialLe (minSet (wand F G)) M := by
    intro p hp
    obtain ⟨a, ha, hka⟩ := exists_min_subheap (hm hp)
    exact (upward_mem_iff _ p.1 p.2).mpr ⟨a, ha, hka⟩
  have hb := hleast.2 _ hk
  have hboth : SpatialLe M (minSet (wand F G)) ∧ M ⊆ minSet (wand F G) := by
    rcases hb with hbad | hgood
    · exact (hbad.2 hkm).elim
    · exact ⟨hgood.1, hgood.2.2⟩
  apply Set.Subset.antisymm hboth.2
  intro p hp
  obtain ⟨a, ha, hma⟩ := (upward_mem_iff M p.1 p.2).mp (hboth.1 hp)
  have he : a = p.2 := hp.2 a ha (hm hma)
  simpa only [he] using hma

end FootprintProof

open BiAbduction.Footprint

namespace FootprintProof

def UpwardClosed (F : Pred) : Prop :=
  ∀ (s : Stack) (h H : Heap), Heap.Subheap h H → (s, h) ∈ F → (s, H) ∈ F

theorem upward_univ : UpwardClosed Set.univ := by
  intro s h H hs hf
  exact Set.mem_univ _

theorem upward_wand {F G : Pred} (hG : UpwardClosed G) : UpwardClosed (wand F G) := by
  intro s h H hs hw a U hu ha
  obtain ⟨u, hu', hus⟩ := union_mono_left hu hs
  exact hG s u U hus (hw a u hu' ha)

theorem upward_sep {P X : Pred} (hX : UpwardClosed X) : UpwardClosed (sepConj P X) := by
  intro s h H hs hh
  obtain ⟨p, x, hu, hp, hx⟩ := hh
  obtain ⟨r, hr⟩ := sub_split (sub_trans (union_sub_left hu) hs)
  exact ⟨p, r, hr, hp, hX s x r (union_cancel_left hu hr hs) hx⟩

theorem safe_upward (α : Action) (C : List Action) : UpwardClosed (safe α C) := by
  induction C generalizing α with
  | nil => exact upward_sep upward_univ
  | cons β C ih => exact upward_sep (upward_wand (ih β))

theorem upward_eq_min_sep_univ {F : Pred} (hF : UpwardClosed F) :
    F = sepConj (minSet F) Set.univ := by
  ext p
  constructor
  · intro hp
    obtain ⟨a, ha, hmin⟩ := exists_min_subheap hp
    exact (upward_mem_iff _ p.1 p.2).mpr ⟨a, ha, hmin⟩
  · intro hp
    obtain ⟨a, ha, hmin⟩ := (upward_mem_iff _ p.1 p.2).mp hp
    exact hF p.1 a p.2 ha hmin.1

theorem safe_eq_foot_sep_true (α : Action) (C : List Action) :
    safe α C = sepConj (foot α C) Set.univ :=
  upward_eq_min_sep_univ (safe_upward α C)

end FootprintProof

open BiAbduction.Footprint

namespace FootprintProof

theorem precise_min_eq {P : Pred} (hP : IsPrecise P) : minSet P = P := by
  apply Set.Subset.antisymm (minSet_subset P)
  intro p hp
  refine ⟨hp, ?_⟩
  intro h' hh' hp'
  exact hP p.1 p.2 h' p.2 hh' (sub_refl _) hp' hp

theorem min_sep_eq {P X : Pred} (hP : IsPrecise P) :
    minSet (sepConj P X) = sepConj P (minSet X) := by
  ext p
  constructor
  · intro hh
    obtain ⟨a, b, hu, ha, hb⟩ := hh.1
    refine ⟨a, b, hu, ha, hb, ?_⟩
    intro b' hs hb'
    obtain ⟨h', hu', hh'⟩ := union_mono_right hu hs
    have he : h' = p.2 := hh.2 h' hh' ⟨a, b', hu', ha, hb'⟩
    apply sub_antisymm hs
    exact union_cancel_left hu hu' (he ▸ sub_refl h')
  · rintro ⟨a, b, hu, ha, hb⟩
    refine ⟨⟨a, b, hu, ha, hb.1⟩, ?_⟩
    intro h' hh' hmem
    obtain ⟨a', b', hu', ha', hb'⟩ := hmem
    have he : a' = a := hP p.1 p.2 a' a
      (sub_trans (union_sub_left hu') hh') (union_sub_left hu) ha' ha
    subst a'
    have hbsub : Heap.Subheap b' b := union_cancel_left hu' hu hh'
    have hbeq : b' = b := hb.2 b' hbsub hb'
    subst b'
    exact union_ext hu' hu

theorem min_sep_univ_eq {P : Pred} (hP : IsPrecise P) :
    minSet (sepConj P Set.univ) = P := by
  ext p
  constructor
  · intro hp
    obtain ⟨a, ha, hpa⟩ := (upward_mem_iff P p.1 p.2).mp hp.1
    have he : a = p.2 := hp.2 a ha
      ((upward_mem_iff P p.1 a).mpr ⟨a, sub_refl a, hpa⟩)
    simpa only [he] using hpa
  · intro hp
    refine ⟨(upward_mem_iff P p.1 p.2).mpr ⟨p.2, sub_refl _, hp⟩, ?_⟩
    intro h' hh' hmem
    obtain ⟨a, ha, hpa⟩ := (upward_mem_iff P p.1 h').mp hmem
    have he : a = p.2 := hP p.1 p.2 a p.2 (sub_trans ha hh') (sub_refl _) hpa hp
    exact sub_antisymm hh' (he ▸ ha)

end FootprintProof

namespace BiAbduction.Footprint

/-- Theorem 4.11 (Deriving Footprint, p. 50): if the precondition of every action of the sequence
`α; C` is precise and `P` is the precondition of the canonical spec of `α; C` obtained when
every bi-abduction call delivers the best anti-frame, then `foot(α; C) = P`. -/
theorem theorem_4_11 (α : Action) (C : List Action) (P : Pred)
    (hprec : ∀ a ∈ α :: C, IsPrecise a.pre) (hcanon : IsCanonPre α C P) :
    foot α C = P := by
  revert hprec
  induction hcanon with
  | single α =>
      intro hprec
      exact FootprintProof.min_sep_univ_eq (hprec α (by simp))
  | cons α β C PC M hcanon hleast ih =>
      intro hprec
      have ht : ∀ a ∈ β :: C, IsPrecise a.pre := by
        intro a ha
        exact hprec a (List.mem_cons_of_mem α ha)
      have hs : safe β C = sepConj PC Set.univ := by
        rw [FootprintProof.safe_eq_foot_sep_true, ih ht]
      change minSet (sepConj α.pre (wand α.post (safe β C))) = sepConj α.pre M
      rw [hs, FootprintProof.min_sep_eq (hprec α (by simp)),
        FootprintProof.least_solution_eq hleast]

end BiAbduction.Footprint

theorem solution (α : Action) (C : List Action) (P : Pred)
    (hprec : ∀ a ∈ α :: C, IsPrecise a.pre) (hcanon : IsCanonPre α C P) :
    foot α C = P :=
  BiAbduction.Footprint.theorem_4_11 α C P hprec hcanon
