-- Prove2me | solution 1 for ErdosPosa.not_adj_of_deg_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:30:44.675575+00:00
-- url     : https://prove2.me/submissions/72fd75ec-a5c9-4d68-9ffc-ea8b5448d11f

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Theorems.Thm_ErdosPosa_neighborSet_empty_of_deg_zero

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution [Finite V] {H : SimpleGraph V} {v w : V} (h : deg H v = 0) :
    ¬ H.Adj v w := by
  intro hvw
  have : w ∈ H.neighborSet v := hvw
  rw [neighborSet_empty_of_deg_zero h] at this
  exact this
end ErdosPosa
