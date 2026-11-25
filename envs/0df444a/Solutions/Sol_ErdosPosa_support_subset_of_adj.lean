-- Prove2me | solution 1 for ErdosPosa.support_subset_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:20:21.220837+00:00
-- url     : https://prove2.me/submissions/14e447df-0aa9-4a31-8d09-716fd26e4e02

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution {G : SimpleGraph V} {T : Set V} (hG : ∀ a b, G.Adj a b → b ∈ T)
    {u v : V} (p : G.Walk u v) (hu : u ∈ T) : ∀ x ∈ p.support, x ∈ T := by
  induction p with
  | nil => intro x hx; rw [Walk.support_nil, List.mem_singleton] at hx; exact hx ▸ hu
  | cons hadj p ih =>
    intro x hx
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hu
    · exact ih (hG _ _ hadj) x hx
end ErdosPosa
