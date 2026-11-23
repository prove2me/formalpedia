-- Prove2me | solution 1 for BhangaleHypergraph.Main.composition
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:42:18.849843+00:00
-- url     : https://prove2.me/submissions/382a213a-ce1d-49aa-ac19-72c74ce4dbdc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BhangaleHypergraph_Main_relational_completeness
import Theorems.Thm_BhangaleHypergraph_Main_relational_soundness
import Theorems.Thm_BhangaleHypergraph_Main_simple_conversion
import Definitions.Def_BhangaleHypergraph_Main_Relational

open BhangaleHypergraph.Main

theorem solution (G : Outer) (C n : ℕ) (hC : 2 ≤ C) (hlayers : G.layers = C + 1)
    (numbering : Fin n ≃ RelVertex G.toLayered C × Fin (2 * C + 1)) :
    (Satisfiable G.toLayered → (Composed G.toLayered C n numbering).Colorable 2) ∧
    (∀ ε : ℝ, PairwiseSound G ε →
      ε < 1 / ((Nat.choose (C + 1) 2 : ℝ) * ((2 * C : ℕ) : ℝ) ^ (2 * C)) →
        ¬ (Composed G.toLayered C n numbering).Colorable C) := by
  unfold Composed
  constructor
  · intro hsat
    exact (simple_conversion (Relational G.toLayered C) C n hC numbering).1
      (relational_completeness G.toLayered C hC hlayers hsat)
  · intro ε hsound hε hcolor
    exact relational_soundness G C hC hlayers ε hsound hε
      ((simple_conversion (Relational G.toLayered C) C n hC numbering).2 hcolor)
