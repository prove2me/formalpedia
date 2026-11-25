-- Prove2me | solution 1 for CliqueMinors.contract_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:43.810799+00:00
-- url     : https://prove2.me/submissions/300d63f9-d183-47cf-832b-4adf2618c7a7

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
omit [Fintype V]
namespace CliqueMinors
theorem _root_.solution {G : SimpleGraph V} {S : Finset V} {x y : V} (hxy : G.Adj x y)
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) :
    ∀ a b, (contractG G x y).Adj a b → a ∈ S.erase y := by
  intro a b h
  refine Finset.mem_erase.2 ⟨h.2.1, ?_⟩
  rcases h.2.2.2 with h | ⟨rfl, _⟩ | ⟨_, h⟩
  · exact hsupp _ _ h
  · exact hsupp _ _ hxy
  · exact hsupp _ _ h.symm
end CliqueMinors
