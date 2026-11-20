-- Prove2me | solution 1 for DeletionCode.ObstructionProbability.obstruction_probability_le_of_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:20:34.427096+00:00
-- url     : https://prove2.me/submissions/c23b5561-c3dd-4ed1-a5f2-6a783fb2012c

import Definitions.Def_DeletionCode_VerifiedConflictGraphWitness
import Definitions.Def_DeletionCode_WitnessCounting
import Definitions.Def_DeletionCode_RandomHash
import Definitions.Def_DeletionCode_ObstructionProbability
import Theorems.Thm_DeletionCode_ObstructionProbability_candidate_probability_le
import Theorems.Thm_DeletionCode_ObstructionProbability_obstructionEvent_subset_union

set_option autoImplicit true
open DeletionCode DeletionCode.ObstructionProbability
open MeasureTheory Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open CircleHash CircleUniform ConflictGraphWitness WitnessCounting
open scoped BigOperators ENNReal
variable {n : ℕ}
namespace DeletionCode.ObstructionProbability
theorem _root_.solution (t k Q : ℕ) (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (x : Bits n) (hx : KUnique (padBits x) n k) :
    realWeights (Gram (windowLength k)) (obstructionEvent t k Q x) ≤
      ∑ R ∈ Finset.Icc 2 (cutoff t k),
        (Nat.card {U : RuleSet k // Candidate t (padBits x) n k R U} : ℝ≥0∞) *
          ENNReal.ofReal (2 / (Q : ℝ)) ^ R := by
  calc
    _ ≤ realWeights (Gram (windowLength k))
        (⋃ R ∈ Finset.Icc 2 (cutoff t k), candidateEvent t k Q R x) :=
      measure_mono (obstructionEvent_subset_union t k Q ht hQ x)
    _ ≤ ∑ R ∈ Finset.Icc 2 (cutoff t k),
        realWeights (Gram (windowLength k)) (candidateEvent t k Q R x) :=
      measure_biUnion_finset_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro R hR
      exact candidate_probability_le t k Q R (by omega)
        (by have h := (Finset.mem_Icc.mp hR).1; omega) x hx hQ
end DeletionCode.ObstructionProbability
