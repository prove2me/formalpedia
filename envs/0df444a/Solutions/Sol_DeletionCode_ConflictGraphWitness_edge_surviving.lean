-- Prove2me | solution 1 for DeletionCode.ConflictGraphWitness.edge_surviving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:47:47.320183+00:00
-- url     : https://prove2.me/submissions/6b7104fd-8e7f-4743-908e-670048a94277

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_WordGraphWitness
import Definitions.Def_DeletionCode_CircleHash
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Theorems.Thm_DeletionCode_ConflictGraphWitness_edge_catalogue
import Theorems.Thm_DeletionCode_CircleHash_equal_hash_labels_survive


set_option autoImplicit true
open DeletionCode DeletionCode.ConflictGraphWitness
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open ConnectedBlocks AlignmentTrace WitnessCases
namespace DeletionCode.ConflictGraphWitness
theorem _root_.solution {t k n Q : ℕ} {H : Spectrum k →+ UnitAddCircle}
    (hQ : 2 ≤ Q) (hcoverage : SeparatedCoverage t k n)
    {x y : Vertex (n := n) t Q H} (hxy : (graph t Q H).Adj x y) :
    spectrum k y.val - spectrum k x.val ∈ surviving t Q H := by
  exact CircleHash.equal_hash_labels_survive H Q hQ (spectrum k x.val)
    (spectrum k y.val) hxy.2.2 (edge_catalogue hcoverage hxy)
end DeletionCode.ConflictGraphWitness
