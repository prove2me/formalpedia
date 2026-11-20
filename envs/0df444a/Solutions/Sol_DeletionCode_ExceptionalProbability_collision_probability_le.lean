-- Prove2me | solution 1 for DeletionCode.ExceptionalProbability.collision_probability_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:52:31.894789+00:00
-- url     : https://prove2.me/submissions/b46168ef-2704-42b6-a082-c4df58ed757e

import Definitions.Def_DeletionCode_RandomHash
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_ExceptionalProbability
import Theorems.Thm_DeletionCode_ExceptionalProbability_spectrum_difference_ne_zero
import Theorems.Thm_DeletionCode_CircleHash_equal_hash_labels_norm_lt
import Theorems.Thm_DeletionCode_RandomHash_real_nonzero_test_probability


set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalProbability
open MeasureTheory Windows HeaderRecovery SignedSupport CircleHash CircleUniform
open ConflictGraphWitness
open scoped BigOperators
variable {n : ℕ}
namespace DeletionCode.ExceptionalProbability
theorem _root_.solution (k Q : ℕ) (x y : Bits n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k ≤ n)
    (hQ : 2 ≤ Q) (hxy : x ≠ y) :
    realWeights (Gram (windowLength k)) (collisionEvent k Q x y) ≤
      ENNReal.ofReal (2 / (Q : ℝ)) := by
  have hsub : collisionEvent k Q x y ⊆
      {weights | ‖realWeightedHash weights (spectrum k y - spectrum k x)‖ < 1 / (Q : ℝ)} := by
    intro weights hlabel
    exact equal_hash_labels_norm_lt (realWeightedHash weights) Q hQ
      (spectrum k x) (spectrum k y) hlabel
  exact (measure_mono hsub).trans_eq
    (RandomHash.real_nonzero_test_probability (spectrum k y - spectrum k x)
      (spectrum_difference_ne_zero k x y hx hn hxy) Q hQ)
end DeletionCode.ExceptionalProbability
