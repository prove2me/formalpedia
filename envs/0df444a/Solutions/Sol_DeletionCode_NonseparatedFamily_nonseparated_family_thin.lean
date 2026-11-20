-- Prove2me | solution 1 for DeletionCode.NonseparatedFamily.nonseparated_family_thin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:19:18.663242+00:00
-- url     : https://prove2.me/submissions/20b88494-f323-467f-a02b-2c22477a0094

import Definitions.Def_DeletionCode_ExceptionalPartnerCount
import Definitions.Def_DeletionCode_NonseparatedFamily
import Theorems.Thm_DeletionCode_NonseparatedFamily_exceptional_probability_bound
import Theorems.Thm_DeletionCode_ExceptionalCountArithmetic_exceptionalConstant_pos


set_option autoImplicit true
open DeletionCode DeletionCode.NonseparatedFamily
open MeasureTheory Windows HeaderRecovery SignedSupport CircleHash CircleUniform ConflictGraphWitness
open ExceptionalProbability ExceptionalPartnerCount ExceptionalCountArithmetic
namespace DeletionCode.NonseparatedFamily
theorem _root_.solution (t : ℕ) (ht : 2 ≤ t) :
    ∃ c : ℕ, 0 < c ∧ ∀ (n k Q : ℕ) (x : Bits n),
      KUnique (padBits x) n k → windowLength k ≤ n → 2 ≤ Q →
        (realWeights (Gram (windowLength k))
          {weights | FiniteConflictGraph.Exceptional t k
            (wordLabel Q (realWeightedHash weights)) x}).toReal ≤
          2 * (c : ℝ) * (n : ℝ) ^ (2 * t - 1) * (windowLength k : ℝ) / Q := by
  refine ⟨exceptionalConstant t, exceptionalConstant_pos (by omega), ?_⟩
  intro n k Q x hx hn hQ
  exact exceptional_probability_bound t k Q x hx hn hQ
end DeletionCode.NonseparatedFamily
