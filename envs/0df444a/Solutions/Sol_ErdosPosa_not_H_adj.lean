-- Prove2me | solution 1 for ErdosPosa.not_H_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:27.838639+00:00
-- url     : https://prove2.me/submissions/cebcfc8b-4fb3-44d3-9940-74b9b574e273

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Definitions.Def_ErdosPosaLib_EPPin
public import Theorems.Thm_ErdosPosa_not_adj_of_deg_zero


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable [Finite V] {G H : SimpleGraph V}
namespace ErdosPosa
theorem _root_.solution {c d a : V} (hcd : c ≠ d) (hc : c = a ∨ deg H c = 0) (hd : d = a ∨ deg H d = 0) :
    ¬ H.Adj c d := by
  rcases hc with rfl | hc
  · rcases hd with rfl | hd
    · exact absurd rfl hcd
    · exact fun h => not_adj_of_deg_zero hd h.symm
  · exact not_adj_of_deg_zero hc
end ErdosPosa
