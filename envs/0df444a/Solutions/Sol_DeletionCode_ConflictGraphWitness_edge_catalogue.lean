-- Prove2me | solution 1 for DeletionCode.ConflictGraphWitness.edge_catalogue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:43:51.259673+00:00
-- url     : https://prove2.me/submissions/7edc9958-da32-4918-9256-24bdaee48f21

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_WordGraphWitness
import Definitions.Def_DeletionCode_CircleHash
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Theorems.Thm_DeletionCode_FiniteConflictGraph_edge_separated_trace
import Theorems.Thm_DeletionCode_FiniteConflictGraph_vertex_unique


set_option autoImplicit true
open DeletionCode DeletionCode.ConflictGraphWitness
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open ConnectedBlocks AlignmentTrace WitnessCases
namespace DeletionCode.ConflictGraphWitness
theorem _root_.solution {t k n Q : ℕ} {H : Spectrum k →+ UnitAddCircle}
    (hcoverage : SeparatedCoverage t k n)
    {x y : Vertex (n := n) t Q H} (hxy : (graph t Q H).Adj x y) :
    CatalogueRule t k (spectrum k y.val - spectrum k x.val) := by
  obtain ⟨trace, hs, ht, hd, hi, hsep⟩ := FiniteConflictGraph.edge_separated_trace hxy
  exact hcoverage x.val y.val (FiniteConflictGraph.vertex_unique x) trace hs ht hd hi hsep
end DeletionCode.ConflictGraphWitness
