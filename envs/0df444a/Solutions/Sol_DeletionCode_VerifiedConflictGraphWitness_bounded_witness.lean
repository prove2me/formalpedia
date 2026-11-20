-- Prove2me | solution 1 for DeletionCode.VerifiedConflictGraphWitness.bounded_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:17:01.113665+00:00
-- url     : https://prove2.me/submissions/0b1f1def-0a50-4949-bf5b-5c0918882414

import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_BubbleCatalogue
import Definitions.Def_DeletionCode_SeparatedTraceCoverage
import Definitions.Def_DeletionCode_VerifiedConflictGraphWitness
import Theorems.Thm_DeletionCode_VerifiedConflictGraphWitness_separated_coverage
import Theorems.Thm_DeletionCode_ConflictGraphWitness_bounded_witness_of_coverage


set_option autoImplicit true
open DeletionCode DeletionCode.VerifiedConflictGraphWitness
open Windows HeaderRecovery CatalogueWords AlignmentTrace
open ConflictGraphWitness SignedSupport SignedRuleCount RuleSetGraph WitnessCases
namespace DeletionCode.VerifiedConflictGraphWitness
theorem _root_.solution {t k n Q : ℕ} (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (H : Spectrum k →+ UnitAddCircle) (x : Vertex (n := n) t Q H)
    (hnot : ¬ ((graph t Q H).connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet k,
      Witness t k (spectrum k x.val) (surviving t Q H) U ∧
      ManuscriptCounting.GeneratingSet t (padBits x.val) n k U.card (componentCount U) U :=
  ConflictGraphWitness.bounded_witness_of_coverage ht hQ H (separated_coverage t k n) x hnot
end DeletionCode.VerifiedConflictGraphWitness
