-- Prove2me | solution 1 for BunkbedAux.wzGraph_abc_eq_alt
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T00:45:11.528214+00:00
-- url     : https://prove2.me/submissions/801d4287-e2ee-467e-833f-46d28d818135

import Definitions.Def_BunkbedHypergraph

open Bunkbed Bunkbed.Hyper Finset SimpleGraph

/-- On a hyperedge whose three vertices are distinct, the `abc` state contributes exactly the
triangle on that triple, which is the clique that the alternative model places there. -/
private lemma edges_abc_eq (i : Fin 6) (l : Fin 2) :
    (WZ.abc).edges (hollomTriple i) l = cliqueAt (hollomE i) l := by
  fin_cases i <;> fin_cases l <;> decide

/-- The `a_b_c` state contributes no edges. -/
private lemma edges_a_b_c (t : Fin 10 × Fin 10 × Fin 10) (l : Fin 2) :
    (WZ.a_b_c).edges t l = ∅ := rfl

private lemma edgeset_eq (σ : Fin 6 → Fin 2) :
    (univ.biUnion (fun p : Fin 6 × Fin 2 =>
        (if p.2 = σ p.1 then WZ.abc else WZ.a_b_c).edges (hollomTriple p.1) p.2))
      = univ.biUnion (fun i : Fin 6 => cliqueAt (hollomE i) (σ i)) := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨i, l, hl⟩
    by_cases h : l = σ i
    · subst h
      exact ⟨i, by rwa [if_pos rfl, edges_abc_eq] at hl⟩
    · rw [if_neg h, edges_a_b_c] at hl
      simp at hl
  · rintro ⟨i, hi⟩
    exact ⟨i, σ i, by rw [if_pos rfl, edges_abc_eq]; exact hi⟩

/-- **The WZ model contains the alternative model.** -/
theorem solution (σ : Fin 6 → Fin 2) :
    wzGraph hollomTriple hollomT (fun p => if p.2 = σ p.1 then WZ.abc else WZ.a_b_c)
      = altBBGraph hollomE hollomT σ := by
  show ofEdges _ = ofEdges _
  rw [edgeset_eq]
