-- Prove2me | solution 1 for DeletionCode.VerifiedConflictGraphWitness.edge_catalogue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:17:01.700196+00:00
-- url     : https://prove2.me/submissions/2fe6d372-f343-41ad-83b1-3550d580c39c

import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_BubbleCatalogue
import Definitions.Def_DeletionCode_SeparatedTraceCoverage
import Definitions.Def_DeletionCode_VerifiedConflictGraphWitness
import Theorems.Thm_DeletionCode_VerifiedConflictGraphWitness_separated_coverage
import Theorems.Thm_DeletionCode_ConflictGraphWitness_edge_catalogue


set_option autoImplicit true
open DeletionCode DeletionCode.VerifiedConflictGraphWitness
open Windows HeaderRecovery CatalogueWords AlignmentTrace
open ConflictGraphWitness SignedSupport SignedRuleCount RuleSetGraph WitnessCases
namespace DeletionCode.VerifiedConflictGraphWitness
theorem _root_.solution {t k n Q : ℕ} {H : Spectrum k →+ UnitAddCircle}
    {x y : Vertex (n := n) t Q H} (hxy : (graph t Q H).Adj x y) :
    ConnectedBlocks.CatalogueRule t k (spectrum k y.val - spectrum k x.val) :=
  ConflictGraphWitness.edge_catalogue (separated_coverage t k n) hxy
end DeletionCode.VerifiedConflictGraphWitness
