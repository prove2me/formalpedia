-- Prove2me | solution 1 for Conway99Formal.FiniteFields.adjacency_square
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T19:05:20.378623+00:00
-- url     : https://prove2.me/submissions/e0cfcffb-ca13-45d3-87c5-450a5092deb1

import Definitions.Def_FiniteFieldCore
import Mathlib

namespace Conway99Formal.FiniteFields
end Conway99Formal.FiniteFields

set_option autoImplicit false

namespace Conway99Formal.FiniteFields

open Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]



private theorem complement_adjacency (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Type*) [Ring R] [DecidableEq R] :
    Gᶜ.adjMatrix R = J R - 1 - G.adjMatrix R := by
  have h := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := R)
  rw [G.compl_adjMatrix_eq_adjMatrix_compl R] at h
  change Gᶜ.adjMatrix R = (of 1 : Matrix V V R) - 1 - G.adjMatrix R
  linear_combination (norm := module) h


























end Conway99Formal.FiniteFields

set_option autoImplicit false

open Conway99Formal.FiniteFields

open Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

open Conway99Formal.FiniteFields in
theorem solution {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (R : Type*) [Ring R] [DecidableEq R] :
    (G.adjMatrix R) ^ 2 = 12 • (1 : Matrix V V R) - G.adjMatrix R + 2 • Conway99Formal.FiniteFields.J R := by
  have hm := h.matrix_eq (α := R)
  rw [complement_adjacency G R] at hm
  rw [hm]
  module
