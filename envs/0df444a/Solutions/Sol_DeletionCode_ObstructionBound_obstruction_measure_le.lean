-- Prove2me | solution 1 for DeletionCode.ObstructionBound.obstruction_measure_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:25:39.797751+00:00
-- url     : https://prove2.me/submissions/fb652a29-e591-4393-881e-b32b2426e091

import Definitions.Def_DeletionCode_ObstructionProbability
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_ObstructionBound
import Theorems.Thm_DeletionCode_ObstructionBound_candidate_count_le
import Theorems.Thm_DeletionCode_ObstructionBound_survival_term_le
import Theorems.Thm_DeletionCode_ObstructionBound_geometric_tail_le
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_ObstructionProbability_obstruction_probability_le


set_option autoImplicit true
open DeletionCode DeletionCode.ObstructionBound
open MeasureTheory Windows HeaderRecovery SignedSupport SignedRuleCount
open CircleUniform WitnessCounting ObstructionProbability
open scoped BigOperators ENNReal
namespace DeletionCode.ObstructionBound
theorem _root_.solution {n : ℕ} (t k Q : ℕ) (ht : 2 ≤ t) (x : Bits n)
    (hx : KUnique (padBits x) n k) (hn : 1 ≤ n)
    (hL : 4 * t + 2 ≤ windowLength k)
    (hbonus : ∀ R, windowLength k < R → n ≤ 2 ^ R)
    (hQ : 8 * scale t n k ≤ Q) (hQtwo : 2 ≤ Q) :
    realWeights (Gram (windowLength k)) (obstructionEvent t k Q x) ≤
      ENNReal.ofReal (1 / 12 : ℝ) := by
  calc
    _ ≤ ∑ R ∈ Finset.Icc 2 (cutoff t k),
        (Nat.card {U : RuleSet k // Candidate t (padBits x) n k R U} : ENNReal) *
          ENNReal.ofReal (2 / (Q : ℝ)) ^ R := obstruction_probability_le t k Q ht hQtwo x
    _ ≤ ∑ R ∈ Finset.Icc 2 (cutoff t k), ENNReal.ofReal ((1 / 4 : ℝ) ^ R) := by
      apply Finset.sum_le_sum
      intro R hR
      exact survival_term_le _ _ Q R
        (candidate_count_le t ht (padBits x) n k R (Finset.mem_Icc.mp hR).1 hx hn
          (hbonus R) hL (Finset.mem_Icc.mp hR).2) hQ (by omega)
    _ = ENNReal.ofReal (∑ R ∈ Finset.Icc 2 (cutoff t k), (1 / 4 : ℝ) ^ R) :=
      (ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (geometric_tail_le _)
end DeletionCode.ObstructionBound
