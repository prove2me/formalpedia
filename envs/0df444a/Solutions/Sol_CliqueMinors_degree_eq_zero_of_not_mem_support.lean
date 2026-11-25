-- Prove2me | solution 1 for CliqueMinors.degree_eq_zero_of_not_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:41:51.092921+00:00
-- url     : https://prove2.me/submissions/9f6272a1-0533-4eb4-afb4-978a2eeb24ed

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
namespace CliqueMinors
theorem _root_.solution {G : SimpleGraph V} {S : Finset V}
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) {v : V} (hv : v ∉ S) : G.degree v = 0 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw
  exact hv (hsupp _ _ ((mem_neighborFinset _ _ _).1 hw))
end CliqueMinors
