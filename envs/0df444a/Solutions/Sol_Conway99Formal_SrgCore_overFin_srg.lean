-- Prove2me | solution 1 for Conway99Formal.SrgCore.overFin_srg
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T03:22:41.108113+00:00
-- url     : https://prove2.me/submissions/43d21b3b-593d-4c19-bc28-761292323fa0

import Mathlib

namespace Conway99Formal.SrgCore
end Conway99Formal.SrgCore

set_option autoImplicit false

/-! Graph-owned parameter and adjacency identities for a hypothetical SRG(99,14,1,2).
Sources: `Conway99/Conway99/Core.lean` §§1–3, 8.1;
`Conway99/Conway99/Claims/C01srgcorealgebra.lean` §§0, 3, 6;
`Conway99/results/R005_star_complement_square_discriminant.md`.
-/

namespace Conway99Formal.SrgCore

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
























































end Conway99Formal.SrgCore

set_option autoImplicit false

/-! Graph-owned parameter and adjacency identities for a hypothetical SRG(99,14,1,2).
Sources: `Conway99/Conway99/Core.lean` §§1–3, 8.1;
`Conway99/Conway99/Claims/C01srgcorealgebra.lean` §§0, 3, 6;
`Conway99/results/R005_star_complement_square_discriminant.md`.
-/

open Conway99Formal.SrgCore

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

open Conway99Formal.SrgCore in
theorem solution (h : G.IsSRGWith 99 14 1 2)
    [DecidableRel (G.overFin h.card).Adj] :
    (G.overFin h.card).IsSRGWith 99 14 1 2 := by
  classical
  let e : G ≃g G.overFin h.card := G.overFinIso h.card
  have hcommon (u v : V) :
      Fintype.card (G.commonNeighbors u v) =
        Fintype.card ((G.overFin h.card).commonNeighbors (e u) (e v)) := by
    apply Fintype.card_congr
    refine e.toEquiv.subtypeEquiv ?_
    intro w
    change (G.Adj u w ∧ G.Adj v w) ↔
      ((G.overFin h.card).Adj (e u) (e w) ∧
        (G.overFin h.card).Adj (e v) (e w))
    simp only [e.map_adj_iff]
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro w
    have hc : G.degree (e.symm w) = (G.overFin h.card).degree w := by
      simpa only [G.card_neighborSet_eq_degree,
        (G.overFin h.card).card_neighborSet_eq_degree, e.apply_symm_apply] using
        Fintype.card_congr (e.mapNeighborSet (e.symm w))
    exact hc.symm.trans (h.regular.degree_eq (e.symm w))
  · intro w z hwz
    have hwz' : G.Adj (e.symm w) (e.symm z) := by
      apply e.map_adj_iff.mp
      simpa using hwz
    have hc := hcommon (e.symm w) (e.symm z)
    simpa only [e.apply_symm_apply] using hc.symm.trans (h.of_adj _ _ hwz')
  · intro w z hwz hn
    have hne : e.symm w ≠ e.symm z := by
      intro heq
      apply hwz
      simpa using congrArg e heq
    have hn' : ¬ G.Adj (e.symm w) (e.symm z) := by
      intro huv
      apply hn
      have hh := e.map_adj_iff.mpr huv
      simpa using hh
    have hc := hcommon (e.symm w) (e.symm z)
    simpa only [e.apply_symm_apply] using hc.symm.trans (h.of_not_adj hne hn')
