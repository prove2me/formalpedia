-- Prove2me | solution 1 for GallaiRoy.colorable_of_orientation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:15:48.931871+00:00
-- url     : https://prove2.me/submissions/15deb0f4-f269-477e-991b-a0cb0ff74ad3

module
public import Mathlib
public import Definitions.Def_GallaiRoyLib_GallaiRoy
section
@[expose] public section
open SimpleGraph
namespace GallaiRoy
variable {V : Type*}
private lemma transGen_of_mem_isChain {D : V → V → Prop} :
    ∀ {a : V} {l : List V}, List.IsChain D (a :: l) → ∀ w ∈ l, Relation.TransGen D a w
  | a, [], _, w, hw => by simp at hw
  | a, b :: l, h, w, hw => by
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.1 hw with rfl | hw
    · exact .single h.1
    · exact .head h.1 (transGen_of_mem_isChain h.2 w hw)
private lemma nodup_of_isChain {D : V → V → Prop} (hD : ∀ x, ¬ Relation.TransGen D x x) :
    ∀ {l : List V}, List.IsChain D l → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    refine List.nodup_cons.2 ⟨fun ha => hD a (transGen_of_mem_isChain h a ha), ?_⟩
    exact nodup_of_isChain hD h.tail
private lemma isDirectedPath_of_isChain {D o : V → V → Prop} (hDo : ∀ a b, D a b → o a b)
    (hD : ∀ x, ¬ Relation.TransGen D x x) {l : List V} (h : List.IsChain D l) :
    IsDirectedPath o l.get := by
  refine ⟨List.nodup_iff_injective_get.1 (nodup_of_isChain hD h), fun i hi => ?_⟩
  exact hDo _ _ (List.isChain_iff_getElem.1 h i hi)
private lemma exists_longer_of_transGen {D : V → V → Prop} {a b : V} (hab : Relation.TransGen D a b)
    {l : List V} (hl : List.IsChain D (b :: l)) :
    ∃ l', List.IsChain D (a :: l') ∧ l.length < l'.length := by
  induction hab using Relation.TransGen.head_induction_on generalizing l with
  | single h => exact ⟨b :: l, List.isChain_cons_cons.2 ⟨h, hl⟩, by simp⟩
  | head h _ ih =>
    obtain ⟨l', hl', hlen⟩ := ih hl
    exact ⟨_ :: l', List.isChain_cons_cons.2 ⟨h, hl'⟩, by simp; omega⟩
private lemma transGen_sup_edge {D : V → V → Prop} {u v a b : V}
    (h : Relation.TransGen (fun x y => D x y ∨ (x = u ∧ y = v)) a b) :
    Relation.TransGen D a b ∨ (Relation.ReflTransGen D a u ∧ Relation.ReflTransGen D v b) := by
  induction h with
  | single h =>
    rcases h with h | ⟨rfl, rfl⟩
    · exact .inl (.single h)
    · exact .inr ⟨.refl, .refl⟩
  | tail _ h ih =>
    rcases h with h | ⟨rfl, rfl⟩
    · rcases ih with ih | ⟨h1, h2⟩
      · exact .inl (ih.tail h)
      · exact .inr ⟨h1, h2.tail h⟩
    · rcases ih with ih | ⟨h1, _⟩
      · exact .inr ⟨ih.to_reflTransGen, .refl⟩
      · exact .inr ⟨h1, .refl⟩
end GallaiRoy
end
end

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiRoy
variable {V : Type*}
namespace GallaiRoy
theorem _root_.solution [Finite V] (G : SimpleGraph V) (o : V → V → Prop)
    (ho : IsOrientation G o) (k : ℕ)
    (hk : ∀ (m : ℕ) (f : Fin m → V), IsDirectedPath o f → m ≤ k) : G.Colorable k := by
  classical
  -- a maximal acyclic sub-relation of `o`
  obtain ⟨D, ⟨hDo, hDac⟩, hmax⟩ := (Set.toFinite
    {D : V → V → Prop | (∀ a b, D a b → o a b) ∧ ∀ x, ¬ Relation.TransGen D x x}).exists_maximal
    ⟨fun _ _ => False, fun _ _ h => h.elim, fun x h => by
      cases h with | single h => exact h | tail _ h => exact h⟩
  have hbound : ∀ {v : V} {l : List V}, List.IsChain D (v :: l) → l.length + 1 ≤ k := by
    intro v l hl
    simpa using hk _ _ (isDirectedPath_of_isChain hDo hDac hl)
  let P : V → ℕ → Prop := fun v m => ∃ l : List V, List.IsChain D (v :: l) ∧ l.length = m
  let h : V → ℕ := fun v => Nat.findGreatest (P v) k
  have hP0 : ∀ v, P v 0 := fun v => ⟨[], by simp, rfl⟩
  have hspec : ∀ v, P v (h v) := fun v => Nat.findGreatest_spec (Nat.zero_le _) (hP0 v)
  have hlt : ∀ v, h v < k := by
    intro v
    obtain ⟨l, hl, hlen⟩ := hspec v
    have := hbound hl
    omega
  have hmono : ∀ {a b : V}, Relation.TransGen D a b → h b < h a := by
    intro a b hab
    obtain ⟨l, hl, hlen⟩ := hspec b
    obtain ⟨l', hl', hlen'⟩ := exists_longer_of_transGen hab hl
    have : l'.length ≤ h a :=
      Nat.le_findGreatest (by have := hbound hl'; omega) ⟨l', hl', rfl⟩
    omega
  have key : ∀ {u v : V}, o u v → u ≠ v → h u ≠ h v := by
    intro u v huv hne
    by_cases hD : D u v
    · exact (hmono (.single hD)).ne'
    · have hvu : Relation.ReflTransGen D v u := by
        by_contra hvu
        have hmem : (fun x y => D x y ∨ (x = u ∧ y = v)) ∈
            {D : V → V → Prop | (∀ a b, D a b → o a b) ∧ ∀ x, ¬ Relation.TransGen D x x} := by
          refine ⟨fun a b hab => ?_, fun x hx => ?_⟩
          · rcases hab with hab | ⟨rfl, rfl⟩
            · exact hDo a b hab
            · exact huv
          · rcases transGen_sup_edge hx with hx | ⟨h1, h2⟩
            · exact hDac x hx
            · exact hvu (h2.trans h1)
        have := hmax hmem (fun a b hab => Or.inl hab)
        exact hD (this u v (Or.inr ⟨rfl, rfl⟩))
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 hvu with h1 | h1
      · exact absurd h1 hne
      · exact (hmono h1).ne
  refine ⟨Coloring.mk (fun v => ⟨h v, hlt v⟩) fun {u v} huv => ?_⟩
  intro heq
  have heq' : h u = h v := congrArg Fin.val heq
  rcases ho.1 u v huv with h1 | h1
  · exact key h1 huv.ne heq'
  · exact key h1 huv.ne.symm heq'.symm
end GallaiRoy
