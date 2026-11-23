-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.flowCutAnswer_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:34:21.731805+00:00
-- url     : https://prove2.me/submissions/43b88ab4-d109-4c9d-b5e6-580747aeabd2

import Definitions.Def_ChenCapacityTerminals_Exact_ExactExecution

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem solution (G : Network) (r z : ℕ) (flow : ℕ → ℝ) (X : Finset ℕ)
    (h : FlowCutAnswer G r z flow X) : OptimalPair G r z X := by
  classical
  rcases h with ⟨hG, hr, hz, hrz, hX, hflow, hcons, hdiv⟩
  refine ⟨hX, ?_⟩
  intro Y hY
  rcases hY with ⟨⟨hYsub, hYne, hrY⟩, hzY⟩
  have divSum (S : Finset ℕ) :
      (∑ v ∈ S, divergence G flow v) =
        ∑ i : Fin G.arcs.length,
          ((if G.incidence.tail i ∈ S then flow i else 0) -
            (if G.incidence.head i ∈ S then flow i else 0)) := by
    unfold divergence
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_sub_distrib]
    simp
  have htotal : (∑ v ∈ G.vertices, divergence G flow v) = 0 := by
    rw [divSum]
    apply Finset.sum_eq_zero
    intro i hi
    have he := hG G.arcs[i.1] (List.getElem_mem i.isLt)
    simp [Network.incidence, List.get_eq_getElem, he.1, he.2.1]
  have hYsum : (∑ v ∈ Y, divergence G flow v) = divergence G flow z := by
    apply Finset.sum_eq_single z
    · intro v hvY hvz
      exact hcons v (hYsub hvY) (by
        intro hvr
        subst v
        exact hrY hvY) hvz
    · intro hznot
      exact (hznot hzY).elim
  have hrzsum : (∑ v ∈ G.vertices, divergence G flow v) =
      divergence G flow r + divergence G flow z := by
    rw [← Finset.sum_erase_add _ _ hr]
    have hzmem : z ∈ G.vertices.erase r := Finset.mem_erase.mpr ⟨Ne.symm hrz, hz⟩
    have hsingle : (∑ v ∈ G.vertices.erase r, divergence G flow v) =
        divergence G flow z := by
      apply Finset.sum_eq_single z
      · intro v hv hvz
        exact hcons v (Finset.mem_of_mem_erase hv) (Finset.mem_erase.mp hv).1 hvz
      · intro hznot
        exact (hznot hzmem).elim
    rw [hsingle]
    ring
  have hsource : divergence G flow r =
      ∑ i : Fin G.arcs.length,
        ((if G.incidence.head i ∈ Y then flow i else 0) -
          (if G.incidence.tail i ∈ Y then flow i else 0)) := by
    have hrzdiv : divergence G flow r = -divergence G flow z := by
      linarith
    rw [hrzdiv, ← hYsum, divSum]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have listSumFin : ∀ (l : List Arc) (F : Arc → ℝ),
      (l.map F).sum = ∑ i : Fin l.length, F (l.get i) := by
    intro l
    induction l with
    | nil => intro F; simp
    | cons a l ih =>
        intro F
        simp only [List.length_cons]
        rw [List.map_cons, List.sum_cons, Fin.sum_univ_succ]
        simp only [List.get_cons_zero]
        congr 1
        rw [ih F]
        apply Finset.sum_congr rfl
        intro i hi
        simp [List.get_eq_getElem, List.getElem_cons_succ]
  rw [← hdiv, hsource]
  unfold cut weight
  rw [listSumFin]
  apply Finset.sum_le_sum
  intro i hi
  have he := hG G.arcs[i.1] (List.getElem_mem i.isLt)
  have hf0 := (hflow i i.isLt).1
  have hfcap : flow i ≤ G.arcs[i.1].capacity := by
    simpa using (hflow i i.isLt).2
  by_cases ht : G.arcs[i.1].tail ∈ Y <;>
    by_cases hh : G.arcs[i.1].head ∈ Y <;>
      simp [Network.incidence, List.get_eq_getElem, ht, hh, he.1, he.2.1, hf0, hfcap]
