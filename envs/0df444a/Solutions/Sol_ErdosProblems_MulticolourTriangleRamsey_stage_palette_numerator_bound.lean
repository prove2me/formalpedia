-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.stage_palette_numerator_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/ff9edde7-04f6-490c-b92f-ee5e733f9bdd

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (j t : ℕ) :
    j ^ t ≤ (j * t).choose t := by
  have hcard := Fintype.card_le_of_injective
    (transversalPaletteEmbedding j t)
    (transversalPaletteEmbedding j t).injective
  calc
    j ^ t = Fintype.card (Fin t → Fin j) := by simp
    _ ≤ Fintype.card
      ↥((Finset.univ : Finset (Fin (j * t))).powersetCard t) := hcard
    _ = (j * t).choose t := by
      rw [Fintype.card_coe, Finset.card_powersetCard]
      simp
end ErdosProblems.MulticolourTriangleRamsey
