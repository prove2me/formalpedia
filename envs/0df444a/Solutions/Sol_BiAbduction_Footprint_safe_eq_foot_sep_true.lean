-- Prove2me | solution 1 for BiAbduction.Footprint.safe_eq_foot_sep_true
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:24:08.750126+00:00
-- url     : https://prove2.me/submissions/68759c19-7079-49c0-a6c8-ff3541e16623

import Mathlib
import Definitions.Def_BiAbduction_Footprint_Semantics
import Definitions.Def_BiAbduction_Footprint_Footprint

-- carved verbatim out of submission ee3a90ff-7111-49f0-95ff-859702838275, lines 268-277

section
open BiAbduction.Footprint

@[ext] theorem heap_ext {a b : Heap} (h : ∀ l, a.cell l = b.cell l) : a = b := by
  cases a
  cases b
  congr
  funext l
  exact h l

theorem sub_refl (a : Heap) : Heap.Subheap a a := by intro l v h; exact h

theorem sub_trans {a b c : Heap} (hab : Heap.Subheap a b) (hbc : Heap.Subheap b c) :
    Heap.Subheap a c := by intro l v h; exact hbc l v (hab l v h)

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

theorem union_cancel_left {h h' a b b' : Heap} (hu : Heap.IsUnion h a b)
    (hu' : Heap.IsUnion h' a b') (hh : Heap.Subheap h h') : Heap.Subheap b b' := by
  intro l v hv
  have ha : a.cell l = none := (hu.1 l).resolve_right (by simp [hv])
  have hhv : h.cell l = some v := by rw [hu.2 l]; simp [ha, hv]
  have hhv' := hh l v hhv
  rw [hu'.2 l] at hhv'
  simpa [ha] using hhv'

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

theorem solution (α : Action) (C : List Action) :
    safe α C = sepConj (foot α C) Set.univ :=
  upward_eq_min_sep_univ (safe_upward α C)

end
