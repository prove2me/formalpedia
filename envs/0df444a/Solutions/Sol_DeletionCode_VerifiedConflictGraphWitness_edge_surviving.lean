-- Prove2me | solution 1 for DeletionCode.VerifiedConflictGraphWitness.edge_surviving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:17:02.481605+00:00
-- url     : https://prove2.me/submissions/f39d83db-ba0d-43b2-81e4-094b098a708c

import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_BubbleCatalogue
import Definitions.Def_DeletionCode_SeparatedTraceCoverage
import Definitions.Def_DeletionCode_VerifiedConflictGraphWitness
import Theorems.Thm_DeletionCode_VerifiedConflictGraphWitness_separated_coverage
import Theorems.Thm_DeletionCode_ConflictGraphWitness_edge_surviving


set_option autoImplicit true
open DeletionCode DeletionCode.VerifiedConflictGraphWitness
open Windows HeaderRecovery CatalogueWords AlignmentTrace
open ConflictGraphWitness SignedSupport SignedRuleCount RuleSetGraph WitnessCases
namespace DeletionCode.VerifiedConflictGraphWitness
theorem _root_.solution {t k n Q : ℕ} {H : Spectrum k →+ UnitAddCircle}
    (hQ : 2 ≤ Q) {x y : Vertex (n := n) t Q H} (hxy : (graph t Q H).Adj x y) :
    spectrum k y.val - spectrum k x.val ∈ surviving t Q H :=
  ConflictGraphWitness.edge_surviving hQ (separated_coverage t k n) hxy
end DeletionCode.VerifiedConflictGraphWitness
