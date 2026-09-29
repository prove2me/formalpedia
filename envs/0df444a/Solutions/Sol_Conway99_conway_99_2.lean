-- Prove2me | solution 2 for Conway99.conway_99
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-12T11:03:59.968444+00:00
-- url     : https://prove2.me/submissions/ed049fe4-7a8f-413e-9e9f-4897cac11e3d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Theorems.Thm_Conway99_conway_99_triangle_system_exists

open Finset SimpleGraph

namespace Conway99Reduction

/-- The collinearity graph of a family of lines on `Fin 99`. -/
def lineGraph (L : Finset (Finset (Fin 99))) : SimpleGraph (Fin 99) where
  Adj x y := x ≠ y ∧ ∃ l ∈ L, x ∈ l ∧ y ∈ l
  symm := ⟨by
    rintro x y ⟨hne, l, hl, hx, hy⟩
    exact ⟨hne.symm, l, hl, hy, hx⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (L : Finset (Finset (Fin 99))) : DecidableRel (lineGraph L).Adj := by
  intro x y
  unfold lineGraph
  infer_instance

variable {L : Finset (Finset (Fin 99))}

/-- The neighbourhood of `x` is the union of the lines through `x`, with `x` removed. -/
lemma neighborFinset_lineGraph (x : Fin 99) :
    (lineGraph L).neighborFinset x = (L.filter fun l => x ∈ l).biUnion fun l => l.erase x := by
  ext y
  simp only [mem_neighborFinset, mem_biUnion, mem_filter, mem_erase]
  constructor
  · rintro ⟨hne, l, hl, hx, hy⟩
    exact ⟨l, ⟨hl, hx⟩, ⟨fun h => hne (h ▸ rfl), hy⟩⟩
  · rintro ⟨l, ⟨hl, hx⟩, hyx, hy⟩
    exact ⟨fun h => hyx (h ▸ rfl), l, hl, hx, hy⟩

/-- Seven lines through each point, two further points on each line, and no repetitions:
the collinearity graph is 14-regular. -/
lemma degree_lineGraph (h3 : ∀ l ∈ L, l.card = 3)
    (hpl : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → (l₁ ∩ l₂).card ≤ 1)
    (hdeg : ∀ x : Fin 99, (L.filter fun l => x ∈ l).card = 7) (x : Fin 99) :
    (lineGraph L).degree x = 14 := by
  have hcard : ∀ l ∈ L.filter fun l => x ∈ l, (l.erase x).card = 2 := by
    intro l hl
    simp only [mem_filter] at hl
    rw [Finset.card_erase_of_mem hl.2, h3 l hl.1]
  have key : ∀ l₁ ∈ L.filter fun l => x ∈ l, ∀ l₂ ∈ L.filter fun l => x ∈ l, l₁ ≠ l₂ →
      Disjoint (l₁.erase x) (l₂.erase x) := by
    intro l₁ h₁ l₂ h₂ hne
    simp only [mem_filter] at h₁ h₂
    refine Finset.disjoint_left.2 ?_
    intro a ha1' ha2'
    simp only [mem_erase] at ha1' ha2'
    obtain ⟨hax, ha1⟩ := ha1'
    obtain ⟨-, ha2⟩ := ha2'
    have hsub : ({x, a} : Finset (Fin 99)) ⊆ l₁ ∩ l₂ := by
      intro b hb
      simp only [mem_insert, mem_singleton] at hb
      rcases hb with rfl | rfl
      · exact mem_inter.2 ⟨h₁.2, h₂.2⟩
      · exact mem_inter.2 ⟨ha1, ha2⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hax]), Finset.card_singleton] at h1
    have h2 := hpl l₁ h₁.1 l₂ h₂.1 hne
    omega
  rw [SimpleGraph.degree, neighborFinset_lineGraph, Finset.card_biUnion key,
    Finset.sum_congr rfl hcard, Finset.sum_const, hdeg x]
  rfl

lemma card_commonNeighbors_eq {V : Type} [Fintype V] [DecidableEq V] (g : SimpleGraph V)
    [DecidableRel g.Adj] (v w : V) :
    Fintype.card (g.commonNeighbors v w) =
      (g.neighborFinset v ∩ g.neighborFinset w).card := by
  rw [← Set.toFinset_card]
  congr 1
  ext z
  simp [mem_commonNeighbors]

/-- Non-adjacent distinct pairs have exactly two common neighbours. -/
lemma card_common_of_not_adj
    (hmu : ∀ x y : Fin 99, x ≠ y → (∀ l ∈ L, ¬(x ∈ l ∧ y ∈ l)) →
        (univ.filter fun z : Fin 99 => z ≠ x ∧ z ≠ y ∧
            (∃ l ∈ L, x ∈ l ∧ z ∈ l) ∧ (∃ l ∈ L, y ∈ l ∧ z ∈ l)).card = 2)
    (v w : Fin 99) (hvw : v ≠ w) (h : ¬ (lineGraph L).Adj v w) :
    ((lineGraph L).neighborFinset v ∩ (lineGraph L).neighborFinset w).card = 2 := by
  have hnc : ∀ l ∈ L, ¬(v ∈ l ∧ w ∈ l) := fun l hl hmem => h ⟨hvw, l, hl, hmem.1, hmem.2⟩
  rw [← hmu v w hvw hnc]
  congr 1
  ext z
  simp only [mem_inter, mem_neighborFinset, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, l1, hl1, hv1, hz1⟩, ⟨h2, l2, hl2, hw2, hz2⟩⟩
    exact ⟨fun hh => h1 hh.symm, fun hh => h2 hh.symm, ⟨l1, hl1, hv1, hz1⟩, ⟨l2, hl2, hw2, hz2⟩⟩
  · rintro ⟨hzv, hzw, ⟨l1, hl1, hv1, hz1⟩, ⟨l2, hl2, hw2, hz2⟩⟩
    exact ⟨⟨fun hh => hzv hh.symm, l1, hl1, hv1, hz1⟩, ⟨fun hh => hzw hh.symm, l2, hl2, hw2, hz2⟩⟩

/-- Adjacent pairs have at least one common neighbour: the third point of their line. -/
lemma one_le_card_common_of_adj (h3 : ∀ l ∈ L, l.card = 3) (v w : Fin 99)
    (h : (lineGraph L).Adj v w) :
    1 ≤ ((lineGraph L).neighborFinset v ∩ (lineGraph L).neighborFinset w).card := by
  obtain ⟨hvw, l, hl, hv, hw⟩ := h
  have hsub : ({v, w} : Finset (Fin 99)) ⊆ l := by
    intro b hb
    simp only [mem_insert, mem_singleton] at hb
    rcases hb with rfl | rfl <;> assumption
  have hcard : ({v, w} : Finset (Fin 99)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hvw]), Finset.card_singleton]
  have hne : ({v, w} : Finset (Fin 99)) ≠ l := by
    intro hEq
    rw [hEq, h3 l hl] at hcard
    omega
  obtain ⟨z, hzl, hz⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  simp only [mem_insert, mem_singleton, not_or] at hz
  refine Finset.card_pos.2 ⟨z, ?_⟩
  simp only [mem_inter, mem_neighborFinset]
  exact ⟨⟨fun hh => hz.1 hh.symm, l, hl, hv, hzl⟩, ⟨fun hh => hz.2 hh.symm, l, hl, hw, hzl⟩⟩

/-- Double counting of the paths of length two with a fixed endpoint `x`, in a 14-regular
graph on 99 vertices. -/
lemma sum_card_common (g : SimpleGraph (Fin 99)) [DecidableRel g.Adj]
    (hreg : ∀ x, g.degree x = 14) (x : Fin 99) :
    ∑ y ∈ univ.erase x, (g.neighborFinset x ∩ g.neighborFinset y).card = 182 := by
  have step1 : ∀ y : Fin 99, (g.neighborFinset x ∩ g.neighborFinset y).card
      = ∑ k ∈ g.neighborFinset x, if k ∈ g.neighborFinset y then 1 else 0 := by
    intro y
    rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
  simp only [step1]
  rw [Finset.sum_comm]
  have step2 : ∀ k : Fin 99, ∑ y ∈ univ.erase x, (if k ∈ g.neighborFinset y then 1 else 0)
      = ((univ.erase x).filter fun y => k ∈ g.neighborFinset y).card := by
    intro k
    rw [Finset.card_filter]
  simp only [step2]
  have step3 : ∀ k ∈ g.neighborFinset x,
      ((univ.erase x).filter fun y => k ∈ g.neighborFinset y) = (g.neighborFinset k).erase x := by
    intro k _
    ext y
    simp only [mem_filter, mem_erase, mem_univ, and_true, mem_neighborFinset]
    exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
  rw [Finset.sum_congr rfl (fun k hk => by rw [step3 k hk])]
  have step4 : ∀ k ∈ g.neighborFinset x, ((g.neighborFinset k).erase x).card = 13 := by
    intro k hk
    rw [mem_neighborFinset] at hk
    have hx : x ∈ g.neighborFinset k := by
      rw [mem_neighborFinset]
      exact hk.symm
    rw [Finset.card_erase_of_mem hx]
    have := hreg k
    rw [SimpleGraph.degree] at this
    omega
  rw [Finset.sum_congr rfl step4, Finset.sum_const, ← SimpleGraph.degree, hreg x]
  rfl

/-- In a 14-regular graph on 99 vertices in which non-adjacent distinct pairs have exactly two
common neighbours and adjacent pairs have at least one, adjacent pairs have exactly one. -/
lemma card_common_of_adj (g : SimpleGraph (Fin 99)) [DecidableRel g.Adj]
    (hreg : ∀ x, g.degree x = 14)
    (hmu : ∀ v w : Fin 99, v ≠ w → ¬ g.Adj v w →
      (g.neighborFinset v ∩ g.neighborFinset w).card = 2)
    (hone : ∀ v w : Fin 99, g.Adj v w → 1 ≤ (g.neighborFinset v ∩ g.neighborFinset w).card)
    (v w : Fin 99) (h : g.Adj v w) :
    (g.neighborFinset v ∩ g.neighborFinset w).card = 1 := by
  classical
  have hNv : ((univ.erase v).filter fun y => y ∈ g.neighborFinset v) = g.neighborFinset v := by
    ext y
    simp only [mem_filter, mem_erase, mem_univ, and_true, mem_neighborFinset]
    exact ⟨fun hh => hh.2, fun hh => ⟨g.ne_of_adj hh.symm, hh⟩⟩
  have hcard_erase : (univ.erase v).card = 98 := by
    rw [Finset.card_erase_of_mem (mem_univ v)]
    simp
  have hdegv : (g.neighborFinset v).card = 14 := by
    have := hreg v
    rwa [SimpleGraph.degree] at this
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ.erase v)
    (fun y => y ∈ g.neighborFinset v)
    (fun y => (g.neighborFinset v ∩ g.neighborFinset y).card)
  have hcompl_card : ((univ.erase v).filter fun y => y ∉ g.neighborFinset v).card = 84 := by
    have := Finset.card_filter_add_card_filter_not
      (s := univ.erase v) (p := fun y => y ∈ g.neighborFinset v)
    rw [hNv, hdegv, hcard_erase] at this
    omega
  have hcompl_sum : (∑ y ∈ (univ.erase v).filter fun y => y ∉ g.neighborFinset v,
      (g.neighborFinset v ∩ g.neighborFinset y).card) = 168 := by
    have hval : ∀ y ∈ (univ.erase v).filter fun y => y ∉ g.neighborFinset v,
        (g.neighborFinset v ∩ g.neighborFinset y).card = 2 := by
      intro y hy
      simp only [mem_filter, mem_erase, mem_univ, and_true, mem_neighborFinset] at hy
      exact hmu v y (Ne.symm hy.1) hy.2
    rw [Finset.sum_congr rfl hval, Finset.sum_const, hcompl_card]
    rfl
  rw [hNv, hcompl_sum, sum_card_common g hreg v] at hsplit
  have hsum14 : (∑ y ∈ g.neighborFinset v,
      (g.neighborFinset v ∩ g.neighborFinset y).card) = 14 := by omega
  by_contra hne
  have h1 : 1 ≤ (g.neighborFinset v ∩ g.neighborFinset w).card := hone v w h
  have hlt : (∑ _y ∈ g.neighborFinset v, 1) <
      ∑ y ∈ g.neighborFinset v, (g.neighborFinset v ∩ g.neighborFinset y).card := by
    refine Finset.sum_lt_sum (fun i hi => ?_) ⟨w, by rwa [mem_neighborFinset], by omega⟩
    rw [mem_neighborFinset] at hi
    exact hone v i hi
  rw [Finset.sum_const, hdegv, hsum14, smul_eq_mul] at hlt
  omega

end Conway99Reduction

open Conway99 Conway99Reduction in
theorem solution : ∃ (α : Type) (_ : Fintype α) (g : SimpleGraph α)
    (_ : DecidableRel g.Adj), IsSRGWith g 99 14 1 2 := by
  obtain ⟨L, h3, hpl, hdeg, hmu⟩ := conway_99_triangle_system_exists
  refine ⟨Fin 99, inferInstance, lineGraph L, inferInstance, ?_⟩
  have hreg : ∀ x, (lineGraph L).degree x = 14 := degree_lineGraph h3 hpl hdeg
  have hmu' : ∀ v w : Fin 99, v ≠ w → ¬ (lineGraph L).Adj v w →
      ((lineGraph L).neighborFinset v ∩ (lineGraph L).neighborFinset w).card = 2 :=
    fun v w hne h => card_common_of_not_adj hmu v w hne h
  have hone : ∀ v w : Fin 99, (lineGraph L).Adj v w →
      1 ≤ ((lineGraph L).neighborFinset v ∩ (lineGraph L).neighborFinset w).card :=
    fun v w h => one_le_card_common_of_adj h3 v w h
  refine ⟨by simp, hreg, ?_, ?_⟩
  · intro v w h
    rw [card_commonNeighbors_eq]
    exact card_common_of_adj (lineGraph L) hreg hmu' hone v w h
  · intro v w hne h
    rw [card_commonNeighbors_eq]
    exact hmu' v w hne h

