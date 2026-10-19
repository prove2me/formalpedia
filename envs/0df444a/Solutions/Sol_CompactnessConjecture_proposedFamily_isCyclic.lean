-- Prove2me | solution 1 for CompactnessConjecture.proposedFamily_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/1fc32b7d-2691-422a-a716-d5cc65cae4c7

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamily_induction
import Theorems.Thm_CompactnessConjecture_jQuotient_not_acyclic
import Theorems.Thm_CompactnessConjecture_kQuotient_not_acyclic
import Theorems.Thm_CompactnessConjecture_four_cycle_not_acyclic
import Theorems.Thm_CompactnessConjecture_six_cycle_not_acyclic

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution : IsCyclicFamily proposedFamily :=
  proposedFamily_induction (P := fun graph => ¬ graph.graph.IsAcyclic)
    four_cycle_not_acyclic six_cycle_not_acyclic
    (fun _ hf => jQuotient_not_acyclic hf)
    (fun _ hf => kQuotient_not_acyclic hf)
end CompactnessConjecture
