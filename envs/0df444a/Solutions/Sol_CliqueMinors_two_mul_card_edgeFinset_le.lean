-- Prove2me | solution 1 for CliqueMinors.two_mul_card_edgeFinset_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:43.517345+00:00
-- url     : https://prove2.me/submissions/b794b025-4561-40e9-b884-9e6ddd81daf4

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Theorems.Thm_CliqueMinors_sum_degree_support

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
    2 * G.edgeFinset.card ≤ S.card * (S.card - 1) := by
  rw [← sum_degree_support hsupp]
  calc ∑ v ∈ S, G.degree v ≤ ∑ v ∈ S, (S.card - 1) := by
        refine Finset.sum_le_sum fun v hv => ?_
        rw [← card_neighborFinset_eq_degree, ← Finset.card_erase_of_mem hv]
        refine Finset.card_le_card fun w hw => ?_
        rw [mem_neighborFinset] at hw
        exact Finset.mem_erase.2 ⟨hw.ne.symm, hsupp _ _ hw.symm⟩
    _ = S.card * (S.card - 1) := by rw [Finset.sum_const, smul_eq_mul]
end CliqueMinors
