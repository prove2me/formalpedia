-- Prove2me | solution 1 for Balinski61.Whitney.disjoint_paths_of_integral_flow
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:05:46.124504+00:00
-- url     : https://prove2.me/submissions/95e44ead-ba5d-4345-aa84-7443ceb16df8

import Mathlib
import Definitions.Def_Balinski61_Whitney_Graph
import Definitions.Def_Balinski61_Whitney_Network
import Definitions.Def_Balinski61_Whitney_UnitNetwork

set_option autoImplicit false
open Balinski61.Whitney

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) (ps pk : V) (hst : ps ≠ pk)
    (f : G.Path ps pk → ℝ) (hf : IsFlow G (unitCapV ps pk n) (unitCapE ps pk n) ps pk f)
    (hint : ∀ C, ∃ z : ℤ, f C = z) (hval : (n : ℝ) ≤ flowValue G f) :
    HasNDisjointPaths G n ps pk := by
  obtain ⟨hnn, hV, hE⟩ := hf
  have loadV_ge : ∀ (x : V) (S : Finset (G.Path ps pk)),
      (∀ C ∈ S, x ∈ (C : G.Walk ps pk).support) → ∑ C ∈ S, f C ≤ loadV G f x := by
    intro x S hS
    unfold loadV
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro C hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hS C hC
    · intro C _ _
      exact hnn C
  have loadE_ge : ∀ (e : Sym2 V) (S : Finset (G.Path ps pk)),
      (∀ C ∈ S, e ∈ (C : G.Walk ps pk).edges) → ∑ C ∈ S, f C ≤ loadE G f e := by
    intro x S hS
    unfold loadE
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro C hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hS C hC
    · intro C _ _
      exact hnn C
  have hcapV : ∀ x, x ≠ ps → x ≠ pk → unitCapV ps pk n x = 1 := by
    intro x h1 h2
    simp [unitCapV, h1, h2]
  have hle1 : ∀ C, f C ≤ 1 := by
    intro C
    by_contra hC
    push_neg at hC
    obtain ⟨w, hw⟩ := C
    cases w with
    | nil => exact hst rfl
    | cons h q =>
      rename_i v
      by_cases hv : v = pk
      · have hadj : G.Adj ps pk := hv ▸ h
        have he : s(ps, pk) ∈ (SimpleGraph.Walk.cons h q).edges := by
          simp [SimpleGraph.Walk.edges_cons, hv]
        have h1 := loadE_ge s(ps, pk) {⟨SimpleGraph.Walk.cons h q, hw⟩}
          (by intro C hC'; rw [Finset.mem_singleton] at hC'; rw [hC']; exact he)
        have h2 := hE s(ps, pk) (by simpa using hadj)
        have h3 : unitCapE ps pk n s(ps, pk) = 1 := by simp [unitCapE]
        rw [Finset.sum_singleton] at h1
        linarith
      · have hvs : v ∈ (SimpleGraph.Walk.cons h q).support := by simp
        have hvp : v ≠ ps := h.ne.symm
        have h1 := loadV_ge v {⟨SimpleGraph.Walk.cons h q, hw⟩}
          (by intro C hC'; rw [Finset.mem_singleton] at hC'; rw [hC']; exact hvs)
        have h2 := hV v
        rw [hcapV v hvp hv] at h2
        rw [Finset.sum_singleton] at h1
        linarith
  have h01 : ∀ C, f C = 0 ∨ f C = 1 := by
    intro C
    obtain ⟨z, hz⟩ := hint C
    have h0 := hnn C
    have h1 := hle1 C
    rw [hz] at h0 h1 ⊢
    have a1 : 0 ≤ z := by exact_mod_cast h0
    have a2 : z ≤ 1 := by exact_mod_cast h1
    have : z = 0 ∨ z = 1 := by omega
    rcases this with rfl | rfl <;> simp
  let S : Finset (G.Path ps pk) := Finset.univ.filter (fun C => f C = 1)
  have hSval : flowValue G f = S.card := by
    unfold flowValue
    calc ∑ C, f C = ∑ C, (if f C = 1 then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl (fun C _ => by rcases h01 C with h | h <;> simp [h])
      _ = S.card := by rw [Finset.sum_boole]
  have hnS : n ≤ S.card := by
    rw [hSval] at hval
    exact_mod_cast hval
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq hnS
  let e : Fin n ≃ T := (Finset.equivFinOfCardEq hTc).symm
  have hfT : ∀ i, f (e i).1 = 1 := fun i => (Finset.mem_filter.mp (hTS (e i).2)).2
  refine ⟨fun i => ((e i).1 : G.Path ps pk).1, ?_, fun i => ((e i).1).2, ?_⟩
  · intro i j hij
    have h1 : (e i).1 = (e j).1 := Subtype.ext hij
    exact e.injective (Subtype.ext h1)
  · intro i j hij x hxi hxj
    by_contra hx
    push_neg at hx
    have hne : (e i).1 ≠ (e j).1 := fun h => hij (e.injective (Subtype.ext h))
    have h1 := loadV_ge x {(e i).1, (e j).1}
      (by intro C hC; rcases Finset.mem_insert.mp hC with rfl | hC
          · exact hxi
          · rw [Finset.mem_singleton.mp hC]; exact hxj)
    rw [Finset.sum_pair hne, hfT i, hfT j] at h1
    have h2 := hV x
    rw [hcapV x hx.1 hx.2] at h2
    linarith
