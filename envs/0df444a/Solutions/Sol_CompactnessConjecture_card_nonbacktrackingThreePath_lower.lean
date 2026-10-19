-- Prove2me | solution 1 for CompactnessConjecture.card_nonbacktrackingThreePath_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/eacbd1f4-208a-458d-8e6f-4eeb02c5becc

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_card_nonbacktrackingNeighbor
import Theorems.Thm_CompactnessConjecture_fintype_card_sigma_lower

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    G.degree u * (d - 1) ^ 2 ≤
      Fintype.card (NonbacktrackingThreePath G u) := by
  have hstep {previous current : V}
      (hedge : G.Adj current previous) :
      d - 1 ≤ Fintype.card
        (NonbacktrackingNeighbor G previous current) := by
    rw [card_nonbacktrackingNeighbor G hedge]
    exact Nat.sub_le_sub_right (hdegree current) 1
  have hsecond (a : G.neighborSet u) :
      (d - 1) * (d - 1) ≤
        Fintype.card
          (Σ w : NonbacktrackingNeighbor G u (a : V),
            NonbacktrackingNeighbor G (a : V) (w : V)) := by
    apply fintype_card_sigma_lower
    · exact hstep a.property.symm
    · intro w
      exact hstep w.property.1.symm
  have hroot : G.degree u ≤ Fintype.card (G.neighborSet u) := by
    exact (G.card_neighborSet_eq_degree u).symm.le
  have hcount := fintype_card_sigma_lower
    (β := fun a : G.neighborSet u =>
      Σ w : NonbacktrackingNeighbor G u (a : V),
        NonbacktrackingNeighbor G (a : V) (w : V))
    hroot hsecond
  simpa [pow_two] using hcount
end CompactnessConjecture
