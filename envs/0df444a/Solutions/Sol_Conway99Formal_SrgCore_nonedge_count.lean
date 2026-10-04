-- Prove2me | solution 1 for Conway99Formal.SrgCore.nonedge_count
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T03:57:01.002467+00:00
-- url     : https://prove2.me/submissions/d6ad17d9-8ac0-49df-bbb7-05548668d5bd

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
theorem solution (h : G.IsSRGWith 99 14 1 2) : Gᶜ.edgeFinset.card = 4158 := by
  have hs := Gᶜ.sum_degrees_eq_twice_card_edges
  have hc (v : V) : Gᶜ.degree v = 84 := by
    simpa using (h.compl.regular.degree_eq v)
  simp_rw [hc] at hs
  simp only [sum_const, card_univ, nsmul_eq_mul] at hs
  rw [h.card] at hs
  omega
