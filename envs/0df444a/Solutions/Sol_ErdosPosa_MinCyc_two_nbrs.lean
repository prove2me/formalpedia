-- Prove2me | solution 1 for ErdosPosa.MinCyc.two_nbrs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:23:48.806732+00:00
-- url     : https://prove2.me/submissions/3cc6073f-5c24-498e-b9c6-7acb1598d393

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Theorems.Thm_ErdosPosa_cyc_remove_low

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
namespace MinCyc
theorem _root_.solution {H : SimpleGraph V} {T : Set V} (h : MinCyc H T) {x : V} (hx : x ∈ T) :
    ∃ y z, y ∈ T ∧ z ∈ T ∧ y ≠ z ∧ H.Adj x y ∧ H.Adj x z := by
  by_contra hcon
  push Not at hcon
  have := h.2 _ Set.sdiff_subset (cyc_remove_low h.1 (fun y z hy hz hxy hxz => by
    by_contra hyz; exact hcon y z hy hz hyz hxy hxz))
  have hx' : x ∈ T \ {x} := by rw [this]; exact hx
  exact hx'.2 rfl
end MinCyc
end ErdosPosa
