-- Prove2me | solution 1 for DenseTriangleFree.no_odd_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:57:31.62722+00:00
-- url     : https://prove2.me/submissions/595213ad-f192-4bc3-b9ec-9df58375a707

module
public import Mathlib
public import Definitions.Def_JinLib_KeyLemma
public import Definitions.Def_JinLib_Bipartite
public import Theorems.Thm_DenseTriangleFree_adj_of_five
public import Theorems.Thm_DenseTriangleFree_subwalk
public import Theorems.Thm_P2M_DenseTriangleFree_triangle_of_cliqueFree__32533396f53c


set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace DenseTriangleFree
theorem _root_.solution (h3 : G.CliqueFree 3)
    (hcn : ∀ u v, u ≠ v → ¬ G.Adj u v → ∃ w, G.Adj u w ∧ G.Adj v w)
    (hZ : ∀ (a : V) (U : Fin 5 → V), (∀ i, G.Adj (U i) (U (i + 1))) → ∃ i, G.Adj a (U i))
    (a : V) (m : ℕ) : ∀ c : ℕ → V, (∀ i, c (i + m) = c i) → (∀ i, G.Adj (c i) (c (i + 1))) →
      (∀ i, ¬ G.Adj a (c i)) → Odd m → False := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro c hper hc hn hodd
  have hodd' : m % 2 = 1 := Nat.odd_iff.1 hodd
  have short : ∀ s L, 0 < L → L < m → L % 2 = 1 → G.Adj (c (s + L - 1)) (c s) → False := by
    intro s L hL hLm hLo hch
    obtain ⟨h1, h2, h3'⟩ := subwalk hc hn s L hL hch
    exact ih L hLm _ h1 h2 h3' (Nat.odd_iff.2 hLo)
  have chord : ∀ s t, s + 2 ≤ t → t + 2 ≤ s + m → ¬ G.Adj (c s) (c t) := by
    intro s t hst htm hadj
    obtain ⟨d, rfl⟩ : ∃ d, t = s + d := ⟨t - s, by omega⟩
    by_cases hd2 : d % 2 = 0
    · exact short s (d + 1) (by omega) (by omega) (by omega)
        (by rw [show s + (d + 1) - 1 = s + d by omega]; exact hadj.symm)
    · exact short (s + d) (m - d + 1) (by omega) (by omega) (by omega)
        (by rw [show s + d + (m - d + 1) - 1 = s + m by omega, hper]; exact hadj)
  have neq : ∀ s t, s < t → t < s + m → c s ≠ c t := by
    intro s t hst htm heq
    obtain ⟨d, rfl⟩ : ∃ d, t = s + d := ⟨t - s, by omega⟩
    by_cases hd2 : d % 2 = 1
    · refine short s d (by omega) (by omega) hd2 ?_
      rw [heq]
      have := hc (s + d - 1)
      rwa [show s + d - 1 + 1 = s + d by omega] at this
    · refine short (s + d) (m - d) (by omega) (by omega) (by omega) ?_
      rw [← heq]
      have := hc (s + m - 1)
      rwa [show s + m - 1 + 1 = s + m by omega, hper,
        show s + m - 1 = s + d + (m - d) - 1 by omega] at this
  obtain rfl | rfl | rfl | hm7 : m = 1 ∨ m = 3 ∨ m = 5 ∨ 7 ≤ m := by omega
  · have h := hc 0
    rw [hper 0] at h
    exact G.irrefl h
  · have h := hc 2
    rw [show 2 + 1 = 0 + 3 from rfl, hper 0] at h
    exact triangle_of_cliqueFree' h3 (hc 0) (hc 1) h
  · have h := hc 4
    rw [show 4 + 1 = 0 + 5 from rfl, hper 0] at h
    rcases adj_of_five hZ a _ _ _ _ _ (hc 0) (hc 1) (hc 2) (hc 3) h with h | h | h | h | h <;>
      exact hn _ h
  obtain ⟨z, hz0, hz3⟩ := hcn (c 0) (c 3) (neq 0 3 (by omega) (by omega))
    (chord 0 3 (by omega) (by omega))
  have haz : G.Adj a z := by
    rcases adj_of_five hZ a _ _ _ _ _ (hc 0) (hc 1) (hc 2) hz3 hz0.symm with h | h | h | h | h
    all_goals first | exact h | exact absurd h (hn _)
  obtain rfl | hm9 : m = 7 ∨ 9 ≤ m := by omega
  · obtain ⟨z1, hz11, hz14⟩ := hcn (c 1) (c 4) (neq 1 4 (by omega) (by omega))
      (chord 1 4 (by omega) (by omega))
    have haz1 : G.Adj a z1 := by
      rcases adj_of_five hZ a _ _ _ _ _ (hc 1) (hc 2) (hc 3) hz14 hz11.symm with h | h | h | h | h
      all_goals first | exact h | exact absurd h (hn _)
    obtain ⟨z4, hz44, hz47⟩ := hcn (c 4) (c 7) (neq 4 7 (by omega) (by omega))
      (chord 4 7 (by omega) (by omega))
    have haz4 : G.Adj a z4 := by
      rcases adj_of_five hZ a _ _ _ _ _ (hc 4) (hc 5) (hc 6) hz47 hz44.symm with h | h | h | h | h
      all_goals first | exact h | exact absurd h (hn _)
    have hc2z4 : G.Adj (c 2) z4 := by
      rcases adj_of_five hZ (c 2) _ _ _ _ _ (hc 4) (hc 5) (hc 6) hz47 hz44.symm with
        h | h | h | h | h
      · exact absurd h (chord 2 4 (by omega) (by omega))
      · exact absurd h (chord 2 5 (by omega) (by omega))
      · exact absurd h (chord 2 6 (by omega) (by omega))
      · exact absurd h (chord 2 7 (by omega) (by omega))
      · exact h
    rcases adj_of_five hZ z _ _ _ _ _ hz11 hz14.symm hz44 hc2z4.symm (hc 1).symm with
      h | h | h | h | h
    · exact triangle_of_cliqueFree' h3 (hc 0) h.symm hz0.symm
    · exact triangle_of_cliqueFree' h3 haz h haz1.symm
    · exact triangle_of_cliqueFree' h3 (hc 3) h.symm hz3.symm
    · exact triangle_of_cliqueFree' h3 haz h haz4.symm
    · exact triangle_of_cliqueFree' h3 (hc 2) hz3 h
  · have hz5 : G.Adj (c 5) z := by
      rcases adj_of_five hZ (c 5) _ _ _ _ _ (hc 0) (hc 1) (hc 2) hz3 hz0.symm with
        h | h | h | h | h
      · exact absurd h.symm (chord 0 5 (by omega) (by omega))
      · exact absurd h.symm (chord 1 5 (by omega) (by omega))
      · exact absurd h.symm (chord 2 5 (by omega) (by omega))
      · exact absurd h.symm (chord 3 5 (by omega) (by omega))
      · exact h
    have hz6 : G.Adj (c 6) z := by
      rcases adj_of_five hZ (c 6) _ _ _ _ _ (hc 0) (hc 1) (hc 2) hz3 hz0.symm with
        h | h | h | h | h
      · exact absurd h.symm (chord 0 6 (by omega) (by omega))
      · exact absurd h.symm (chord 1 6 (by omega) (by omega))
      · exact absurd h.symm (chord 2 6 (by omega) (by omega))
      · exact absurd h.symm (chord 3 6 (by omega) (by omega))
      · exact h
    exact triangle_of_cliqueFree' h3 (hc 5) hz6 hz5.symm
end DenseTriangleFree
