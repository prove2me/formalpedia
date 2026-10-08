-- Prove2me | solution 1 for Conway99Formal.BinaryCode.image_even
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T19:55:47.41213+00:00
-- url     : https://prove2.me/submissions/1f5e7d42-3cba-4002-80c0-974b0b8d3eef

import Definitions.Def_QaAlgebra_BinaryCode
import Theorems.Thm_Conway99Formal_BinaryCode_all_ones_kernel
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























private theorem binary_square (a : ZMod 2) : a * a = a := by
  simpa only [pow_two] using (ZMod.pow_card a)

private theorem self_dot_eq_sum (u : V → ZMod 2) : u ⬝ᵥ u = ∑ i, u i := by
  simp only [dotProduct, binary_square]


























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
theorem solution (h : G.IsSRGWith 99 14 1 2) (x : V → ZMod 2) :
    (adjacency G).mulVec x ⬝ᵥ (adjacency G).mulVec x = 0 := by
  let e : V → ZMod 2 := fun _ => 1
  have he : (adjacency G).mulVec e = 0 := all_ones_kernel G h
  have hsym : (adjacency G)ᵀ = adjacency G := G.transpose_adjMatrix
  calc
    (adjacency G).mulVec x ⬝ᵥ (adjacency G).mulVec x =
        ∑ i, (adjacency G).mulVec x i := self_dot_eq_sum _
    _ = e ⬝ᵥ (adjacency G).mulVec x := by simp [e, dotProduct]
    _ = x ⬝ᵥ (adjacency G)ᵀ.mulVec e :=
      (Matrix.dotProduct_transpose_mulVec (adjacency G) x e).symm
    _ = 0 := by rw [hsym, he]; simp
