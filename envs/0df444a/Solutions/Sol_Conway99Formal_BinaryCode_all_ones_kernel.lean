-- Prove2me | solution 1 for Conway99Formal.BinaryCode.all_ones_kernel
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T19:04:46.509844+00:00
-- url     : https://prove2.me/submissions/6ef71da3-b4fb-4d68-98f1-ddbb8b6f2b69

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
theorem solution (h : G.IsSRGWith 99 14 1 2) :
    (adjacency G).mulVec (fun _ => (1 : ZMod 2)) = 0 := by
  ext i
  have hi := G.adjMatrix_mulVec_const_apply_of_regular
    (α := ZMod 2) (a := 1) h.regular (v := i)
  have h14 : (14 : ZMod 2) = 0 := by decide
  simpa [adjacency, h14] using hi
