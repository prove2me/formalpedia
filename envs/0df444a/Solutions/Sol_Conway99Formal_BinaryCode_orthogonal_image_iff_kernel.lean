-- Prove2me | solution 1 for Conway99Formal.BinaryCode.orthogonal_image_iff_kernel
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T19:04:47.247631+00:00
-- url     : https://prove2.me/submissions/50c57662-30ef-4ac9-817e-4167f520176e

import Definitions.Def_QaAlgebra_BinaryCode
import Mathlib

namespace Conway99Formal.BinaryCode
end Conway99Formal.BinaryCode

set_option autoImplicit false

/-!
Binary adjacency-code identities for an actual SRG(99,14,1,2).
Sources: Conway99/Conway99/Claims/C01srgcorealgebra.lean §4;
Conway99/Conway99/Claims/C04finitefieldranks.lean §1;
Conway99/results/R003_enriched_binary_code_odd_cross_rank.md §1;
Conway99/results/R017_binary_genus2_smith_weight60.md §1.
-/

namespace Conway99Formal.BinaryCode

open Matrix SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]




















































end Conway99Formal.BinaryCode

set_option autoImplicit false

/-!
Binary adjacency-code identities for an actual SRG(99,14,1,2).
Sources: Conway99/Conway99/Claims/C01srgcorealgebra.lean §4;
Conway99/Conway99/Claims/C04finitefieldranks.lean §1;
Conway99/results/R003_enriched_binary_code_odd_cross_rank.md §1;
Conway99/results/R017_binary_genus2_smith_weight60.md §1.
-/

open Conway99Formal.BinaryCode

open Matrix SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

open Conway99Formal.BinaryCode in
theorem solution (u : V → ZMod 2) :
    (∀ y : V → ZMod 2, u ⬝ᵥ (adjacency G).mulVec y = 0) ↔
      (adjacency G).mulVec u = 0 := by
  have hsym : (adjacency G)ᵀ = adjacency G := G.transpose_adjMatrix
  constructor
  · intro hu
    apply dotProduct_eq_zero_iff.mp
    intro y
    have ht := Matrix.dotProduct_transpose_mulVec (adjacency G) y u
    rw [hsym] at ht
    calc
      (adjacency G).mulVec u ⬝ᵥ y = y ⬝ᵥ (adjacency G).mulVec u :=
        dotProduct_comm _ _
      _ = u ⬝ᵥ (adjacency G).mulVec y := ht
      _ = 0 := hu y
  · intro hu y
    have ht := Matrix.dotProduct_transpose_mulVec (adjacency G) y u
    rw [hsym, hu] at ht
    simpa using ht.symm
