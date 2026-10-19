-- Prove2me | solution 1 for CompactnessConjecture.not_acyclic_of_eight_cycle_copy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/52028890-bdd5-41bc-90e7-932df8b17670

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {α : Type*} {graph : SimpleGraph α}
    (copy : SimpleGraph.Copy (SimpleGraph.cycleGraph 8) graph) :
    ¬ graph.IsAcyclic := by
  intro hacyclic
  have hcycle : (SimpleGraph.cycleGraph 8).IsAcyclic :=
    hacyclic.comap copy.toHom copy.injective
  exact hcycle (SimpleGraph.cycleGraph.cycle 5)
    (SimpleGraph.cycleGraph.isCycle_cycle)
end CompactnessConjecture
