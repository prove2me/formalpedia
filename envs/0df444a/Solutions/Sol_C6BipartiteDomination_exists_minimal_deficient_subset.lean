-- Prove2me | solution 1 for C6BipartiteDomination.exists_minimal_deficient_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:41:51.705857+00:00
-- url     : https://prove2.me/submissions/3d62fda0-7632-42cc-9407-b3493e00cf9f

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    (D W : Finset V) (hCover : neighborsIn G D W = W)
    (hlarge : W.card < D.card) :
    ∃ X ∈ D.powerset,
      (neighborsIn G X W).card < X.card ∧
      ∀ Y, Y ⊆ X → (neighborsIn G Y W).card < Y.card → X.card ≤ Y.card := by
  classical
  let bad := D.powerset.filter fun X => (neighborsIn G X W).card < X.card
  have hDmem : D ∈ D.powerset := Finset.mem_powerset.mpr (by intro _ hx; exact hx)
  have hDneighbors : neighborsIn G D W = W := hCover
  have hbad : D ∈ bad := by
    simp only [bad, Finset.mem_filter]
    exact ⟨hDmem, by simpa [hDneighbors] using hlarge⟩
  obtain ⟨X, hXbad, hmin⟩ := Finset.exists_min_image bad Finset.card ⟨D, hbad⟩
  refine ⟨X, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hXbad).1
  · exact (Finset.mem_filter.mp hXbad).2
  · intro Y hYX hYbad
    have hYpow : Y ∈ D.powerset := Finset.mem_powerset.mpr (hYX.trans (Finset.mem_powerset.mp ((Finset.mem_filter.mp hXbad).1)))
    have hYmem : Y ∈ bad := Finset.mem_filter.mpr ⟨hYpow, hYbad⟩
    exact hmin Y hYmem
end C6BipartiteDomination
