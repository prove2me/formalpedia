-- Prove2me | solution 1 for Conway99.conway_99_triangle_system_of_srg
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-12T11:10:21.143212+00:00
-- url     : https://prove2.me/submissions/35d01cc7-37ba-45fd-bb3d-421e4cc7e320

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

open Finset SimpleGraph

namespace Conway99Triangles

variable {V : Type} [Fintype V] [DecidableEq V] (g : SimpleGraph V) [DecidableRel g.Adj]

/-- The triangles of `g`, as a family of 3-element subsets. -/
def triangles : Finset (Finset V) :=
  univ.filter fun s : Finset V => s.card = 3 ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → g.Adj a b

variable {g}

lemma mem_triangles {s : Finset V} :
    s ∈ triangles g ↔ s.card = 3 ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → g.Adj a b := by
  simp [triangles]

lemma card_common_eq_one (h : g.IsSRGWith 99 14 1 2) {x y : V} (hxy : g.Adj x y) :
    (g.neighborFinset x ∩ g.neighborFinset y).card = 1 := by
  have := h.of_adj x y hxy
  rw [← this, ← Set.toFinset_card]
  congr 1
  ext z
  simp [mem_commonNeighbors]

lemma card_common_eq_two (h : g.IsSRGWith 99 14 1 2) {x y : V} (hxy : x ≠ y)
    (hnadj : ¬ g.Adj x y) :
    (g.neighborFinset x ∩ g.neighborFinset y).card = 2 := by
  have := h.of_not_adj hxy hnadj
  rw [← this, ← Set.toFinset_card]
  congr 1
  ext z
  simp [mem_commonNeighbors]

/-- Every edge lies in a triangle, and conversely two points on a common triangle are adjacent. -/
lemma collinear_iff_adj (h : g.IsSRGWith 99 14 1 2) {x y : V} (hxy : x ≠ y) :
    (∃ l ∈ triangles g, x ∈ l ∧ y ∈ l) ↔ g.Adj x y := by
  constructor
  · rintro ⟨l, hl, hx, hy⟩
    exact (mem_triangles.1 hl).2 x hx y hy hxy
  · intro hadj
    obtain ⟨z, hz⟩ := Finset.card_pos.1 (by rw [card_common_eq_one h hadj]; norm_num)
    rw [mem_inter, mem_neighborFinset, mem_neighborFinset] at hz
    refine ⟨{x, y, z}, mem_triangles.2 ⟨?_, ?_⟩, by simp, by simp⟩
    · rw [Finset.card_insert_of_notMem (by simp [hxy, g.ne_of_adj hz.1]),
        Finset.card_insert_of_notMem (by simp [g.ne_of_adj hz.2]),
        Finset.card_singleton]
    · intro a ha b hb hab
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first
          | exact absurd rfl hab
          | assumption
          | exact hadj
          | exact hadj.symm
          | exact hz.1
          | exact hz.2
          | exact hz.1.symm
          | exact hz.2.symm

/-- Two distinct triangles share at most one vertex. -/
lemma triangles_inter_card_le_one (h : g.IsSRGWith 99 14 1 2) {t₁ : Finset V}
    (h₁ : t₁ ∈ triangles g) {t₂ : Finset V} (h₂ : t₂ ∈ triangles g) (hne : t₁ ≠ t₂) :
    (t₁ ∩ t₂).card ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hcon
  rw [mem_inter] at hx hy
  obtain ⟨hc₁, hadj₁⟩ := mem_triangles.1 h₁
  obtain ⟨hc₂, hadj₂⟩ := mem_triangles.1 h₂
  have hxyadj : g.Adj x y := hadj₁ x hx.1 y hy.1 hxy
  -- the third vertices
  have third : ∀ t : Finset V, t ∈ triangles g → x ∈ t → y ∈ t →
      ∃ z ∈ g.neighborFinset x ∩ g.neighborFinset y, t = {x, y, z} := by
    intro t ht htx hty
    obtain ⟨hc, hadj⟩ := mem_triangles.1 ht
    have hsub : ({x, y} : Finset V) ⊆ t := by
      intro b hb
      simp only [mem_insert, mem_singleton] at hb
      rcases hb with rfl | rfl <;> assumption
    have hcard2 : ({x, y} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    have hssub : ({x, y} : Finset V) ⊂ t :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by intro hEq; rw [hEq, hc] at hcard2; omega⟩
    obtain ⟨z, hzt, hz⟩ := Finset.exists_of_ssubset hssub
    simp only [mem_insert, mem_singleton, not_or] at hz
    refine ⟨z, ?_, ?_⟩
    · rw [mem_inter, mem_neighborFinset, mem_neighborFinset]
      exact ⟨hadj x htx z hzt (Ne.symm hz.1), hadj y hty z hzt (Ne.symm hz.2)⟩
    · refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro b hb
        simp only [mem_insert, mem_singleton] at hb
        rcases hb with rfl | rfl | rfl <;> assumption
      · rw [hc, Finset.card_insert_of_notMem (by simp [hxy, Ne.symm hz.1]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hz.2]), Finset.card_singleton]
  obtain ⟨z₁, hz₁, ht₁⟩ := third t₁ h₁ hx.1 hy.1
  obtain ⟨z₂, hz₂, ht₂⟩ := third t₂ h₂ hx.2 hy.2
  have : z₁ = z₂ := by
    have hcard := card_common_eq_one h hxyadj
    rw [Finset.card_eq_one] at hcard
    obtain ⟨a, ha⟩ := hcard
    rw [ha, mem_singleton] at hz₁ hz₂
    rw [hz₁, hz₂]
  exact hne (by rw [ht₁, ht₂, this])

/-- Each vertex lies on exactly seven triangles. -/
lemma card_triangles_through (h : g.IsSRGWith 99 14 1 2) (x : V) :
    ((triangles g).filter fun l => x ∈ l).card = 7 := by
  classical
  set T := (triangles g).filter fun l => x ∈ l with hT
  -- each neighbour of `x` lies on exactly one triangle through `x`
  have hunique : ∀ y ∈ g.neighborFinset x, (T.filter fun t => y ∈ t).card = 1 := by
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨l, hl, hxl, hyl⟩ := (collinear_iff_adj h (g.ne_of_adj hy)).2 hy
    rw [Finset.card_eq_one]
    refine ⟨l, ?_⟩
    apply Finset.eq_singleton_iff_unique_mem.2
    refine ⟨by simp [hT, mem_filter, hl, hxl, hyl], ?_⟩
    intro t ht
    simp only [hT, mem_filter] at ht
    by_contra hne
    have := triangles_inter_card_le_one h ht.1.1 hl hne
    have h2 : ({x, y} : Finset V) ⊆ t ∩ l := by
      intro b hb
      simp only [mem_insert, mem_singleton] at hb
      rcases hb with rfl | rfl
      · exact mem_inter.2 ⟨ht.1.2, hxl⟩
      · exact mem_inter.2 ⟨ht.2, hyl⟩
    have h3 := Finset.card_le_card h2
    rw [Finset.card_insert_of_notMem (by simp [g.ne_of_adj hy]), Finset.card_singleton] at h3
    omega
  -- each triangle through `x` contains exactly two neighbours of `x`
  have hpair : ∀ t ∈ T, ((g.neighborFinset x).filter fun y => y ∈ t).card = 2 := by
    intro t ht
    simp only [hT, mem_filter] at ht
    obtain ⟨hc, hadj⟩ := mem_triangles.1 ht.1
    have hEq : ((g.neighborFinset x).filter fun y => y ∈ t) = t.erase x := by
      ext y
      simp only [mem_filter, mem_erase, mem_neighborFinset]
      exact ⟨fun hh => ⟨g.ne_of_adj hh.1.symm, hh.2⟩,
        fun hh => ⟨hadj x ht.2 y hh.2 (Ne.symm hh.1), hh.2⟩⟩
    rw [hEq, Finset.card_erase_of_mem ht.2, hc]
  -- double count the pairs (neighbour of x, triangle through x containing it)
  have hswap : ∑ y ∈ g.neighborFinset x, (T.filter fun t => y ∈ t).card
      = ∑ t ∈ T, ((g.neighborFinset x).filter fun y => y ∈ t).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl hunique, Finset.sum_congr rfl hpair, Finset.sum_const,
    Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one] at hswap
  have hdeg : (g.neighborFinset x).card = 14 := by
    have := h.regular x
    rwa [SimpleGraph.degree] at this
  omega

end Conway99Triangles

-- A strongly regular graph with parameters (99, 14, 1, 2) yields a line system: its triangles
-- form a partial linear space with seven lines through each point in which any two non-collinear
-- points are simultaneously collinear with exactly two points.
open Conway99Triangles in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (g : SimpleGraph V) [DecidableRel g.Adj] (h : g.IsSRGWith 99 14 1 2) :
    ∃ L : Finset (Finset V),
      (∀ l ∈ L, l.card = 3) ∧
      (∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → (l₁ ∩ l₂).card ≤ 1) ∧
      (∀ x : V, (L.filter fun l => x ∈ l).card = 7) ∧
      (∀ x y : V, x ≠ y → (∀ l ∈ L, ¬(x ∈ l ∧ y ∈ l)) →
        (univ.filter fun z : V => z ≠ x ∧ z ≠ y ∧
            (∃ l ∈ L, x ∈ l ∧ z ∈ l) ∧ (∃ l ∈ L, y ∈ l ∧ z ∈ l)).card = 2) := by
  refine ⟨triangles g, fun l hl => (mem_triangles.1 hl).1,
    fun l₁ h₁ l₂ h₂ hne => triangles_inter_card_le_one h h₁ h₂ hne,
    card_triangles_through h, ?_⟩
  intro x y hxy hnc
  have hnadj : ¬ g.Adj x y := by
    intro hadj
    obtain ⟨l, hl, hx, hy⟩ := (collinear_iff_adj h hxy).2 hadj
    exact hnc l hl ⟨hx, hy⟩
  rw [← card_common_eq_two h hxy hnadj]
  congr 1
  ext z
  simp only [mem_filter, mem_univ, true_and, mem_inter, mem_neighborFinset]
  constructor
  · rintro ⟨hzx, hzy, hcx, hcy⟩
    exact ⟨(collinear_iff_adj h (Ne.symm hzx)).1 hcx,
      (collinear_iff_adj h (Ne.symm hzy)).1 hcy⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Ne.symm (g.ne_of_adj h1), Ne.symm (g.ne_of_adj h2),
      (collinear_iff_adj h (g.ne_of_adj h1)).2 h1,
      (collinear_iff_adj h (g.ne_of_adj h2)).2 h2⟩

