-- Prove2me | solution 1 for DeletionCode.VerifiedConflictGraphWitness.unique_zero_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:00:05.489352+00:00
-- url     : https://prove2.me/submissions/806d2a5e-bced-4d5d-80fc-023df38983cd

import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_BubbleCatalogue
import Definitions.Def_DeletionCode_SeparatedTraceCoverage
import Definitions.Def_DeletionCode_VerifiedConflictGraphWitness

set_option autoImplicit true
open DeletionCode DeletionCode.VerifiedConflictGraphWitness
open Windows HeaderRecovery CatalogueWords AlignmentTrace
open ConflictGraphWitness SignedSupport SignedRuleCount RuleSetGraph WitnessCases
namespace DeletionCode.VerifiedConflictGraphWitness
theorem _root_.solution {n : ℕ} {x : Letters} (hx : KUnique x n 0) : n = 0 := by
  by_contra hn
  have heq : 0 = 1 := hx 0 1 (by omega) (by omega) (by intro i hi; omega)
  omega
end DeletionCode.VerifiedConflictGraphWitness
