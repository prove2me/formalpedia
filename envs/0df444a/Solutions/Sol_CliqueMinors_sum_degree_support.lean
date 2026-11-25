-- Prove2me | solution 1 for CliqueMinors.sum_degree_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:42:51.341742+00:00
-- url     : https://prove2.me/submissions/e6f3efbe-4d0d-4145-a1b3-46ac8172ee1a

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Theorems.Thm_CliqueMinors_degree_eq_zero_of_not_mem_support

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
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) :
    ∑ v ∈ S, G.degree v = 2 * G.edgeFinset.card := by
  rw [← sum_degrees_eq_twice_card_edges]
  refine Finset.sum_subset (Finset.subset_univ _) fun v _ hv => ?_
  exact degree_eq_zero_of_not_mem_support hsupp hv
end CliqueMinors
