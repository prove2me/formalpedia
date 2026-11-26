-- Prove2me | solution 1 for C6BipartiteDomination.paper11_all_compensation_subset_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:05.12911+00:00
-- url     : https://prove2.me/submissions/c6ab0df4-9d48-4f2b-9c03-4f7cd60753c8

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11AllCompensation_subset_S
import Theorems.Thm_C6BipartiteDomination_paper11AllCompensation_charge_four

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    paper11AllCompensation G D hCan hmax ⊆
      paper11NonnegativeSupports G D := by
  intro q hq
  have hS := paper11AllCompensation_subset_S G hCan hmax hq
  have hq4 := paper11AllCompensation_charge_four G hCan hmax hq
  apply Finset.mem_sdiff.mpr
  refine ⟨hS, ?_⟩
  intro hneg
  have hneg' := (Finset.mem_filter.mp hneg).2
  omega
end C6BipartiteDomination
