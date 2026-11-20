-- Prove2me | solution 1 for DeletionCode.ConflictGraphWitness.bounded_witness_of_coverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:08:20.602154+00:00
-- url     : https://prove2.me/submissions/ab9ba0ac-15b1-4a1b-9386-3d9ef268d959

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_WordGraphWitness
import Definitions.Def_DeletionCode_CircleHash
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Theorems.Thm_DeletionCode_ConflictGraphWitness_edge_catalogue
import Theorems.Thm_DeletionCode_ConflictGraphWitness_edge_surviving
import Theorems.Thm_DeletionCode_FiniteConflictGraph_vertex_unique
import Theorems.Thm_DeletionCode_WordGraphWitness_component_witness


set_option autoImplicit true
open DeletionCode DeletionCode.ConflictGraphWitness
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open ConnectedBlocks AlignmentTrace WitnessCases
namespace DeletionCode.ConflictGraphWitness
theorem _root_.solution {t k n Q : ℕ} (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (H : Spectrum k →+ UnitAddCircle) (hcoverage : SeparatedCoverage t k n)
    (x : Vertex (n := n) t Q H)
    (hnot : ¬ ((graph t Q H).connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet k,
      Witness t k (spectrum k x.val) (surviving t Q H) U ∧
      ManuscriptCounting.GeneratingSet t (padBits x.val) n k U.card (componentCount U) U := by
  exact WordGraphWitness.component_witness ht (graph t Q H) (fun v => padBits v.val)
    (surviving t Q H) FiniteConflictGraph.vertex_unique
    (fun h => edge_catalogue hcoverage h) (fun h => edge_surviving hQ hcoverage h) x hnot
end DeletionCode.ConflictGraphWitness
