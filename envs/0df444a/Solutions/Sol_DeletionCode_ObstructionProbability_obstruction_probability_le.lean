-- Prove2me | solution 1 for DeletionCode.ObstructionProbability.obstruction_probability_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:22:46.377753+00:00
-- url     : https://prove2.me/submissions/6597927d-5ea4-4860-a9c4-b537938863f8

import Definitions.Def_DeletionCode_VerifiedConflictGraphWitness
import Definitions.Def_DeletionCode_WitnessCounting
import Definitions.Def_DeletionCode_RandomHash
import Definitions.Def_DeletionCode_ObstructionProbability
import Theorems.Thm_DeletionCode_ObstructionProbability_obstruction_probability_le_of_unique
import Theorems.Thm_DeletionCode_ObstructionProbability_obstructionEvent_empty_of_not_unique

set_option autoImplicit true
open DeletionCode DeletionCode.ObstructionProbability
open MeasureTheory Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open CircleHash CircleUniform ConflictGraphWitness WitnessCounting
open scoped BigOperators ENNReal
variable {n : ℕ}
namespace DeletionCode.ObstructionProbability
theorem _root_.solution (t k Q : ℕ) (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (x : Bits n) :
    realWeights (Gram (windowLength k)) (obstructionEvent t k Q x) ≤
      ∑ R ∈ Finset.Icc 2 (cutoff t k),
        (Nat.card {U : RuleSet k // Candidate t (padBits x) n k R U} : ℝ≥0∞) *
          ENNReal.ofReal (2 / (Q : ℝ)) ^ R := by
  classical
  by_cases hx : KUnique (padBits x) n k
  · exact obstruction_probability_le_of_unique t k Q ht hQ x hx
  · rw [obstructionEvent_empty_of_not_unique t k Q x hx, measure_empty]
    exact bot_le
end DeletionCode.ObstructionProbability
