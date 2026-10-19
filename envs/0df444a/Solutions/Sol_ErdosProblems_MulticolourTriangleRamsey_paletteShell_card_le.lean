-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.paletteShell_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/786dc9a0-ab0b-4675-a990-8cf6050de3cd

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (N t d : ℕ)
    (Q : Finset (Fin N)) (hQ : Q.card = t) :
    (paletteShell N t Q d).card ≤
      t.choose d * (N - t).choose d := by
  classical
  have hcard := Fintype.card_le_of_injective
    (paletteShellEmbedding N t d Q hQ)
    (paletteShellEmbedding N t d Q hQ).injective
  calc
    (paletteShell N t Q d).card = Fintype.card ↥(paletteShell N t Q d) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card
      (↥(Q.powersetCard d) ×
        ↥(((Finset.univ : Finset (Fin N)) \ Q).powersetCard d)) := hcard
    _ = t.choose d * (N - t).choose d := by
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
        Finset.card_powersetCard, Finset.card_powersetCard,
        Finset.card_sdiff_of_subset (Finset.subset_univ Q)]
      simp [hQ]
end ErdosProblems.MulticolourTriangleRamsey
