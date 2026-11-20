-- Prove2me | solution 1 for DeletionCode.PaperProbability.obstructions_are_rare
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:30:32.018098+00:00
-- url     : https://prove2.me/submissions/6a10393c-43c2-4c00-92f2-0794b230d78b

import Definitions.Def_DeletionCode_NonseparatedFamily
import Definitions.Def_DeletionCode_ObstructionBound
import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_PaperProbability
import Theorems.Thm_DeletionCode_PaperProbability_labels_ge_two
import Theorems.Thm_DeletionCode_ObstructionBound_obstruction_measure_le
import Theorems.Thm_DeletionCode_PaperParameters_eventually_ready
import Theorems.Thm_DeletionCode_PaperParameters_le_two_pow_of_L_lt


set_option autoImplicit true
open DeletionCode DeletionCode.PaperProbability
open MeasureTheory Windows HeaderRecovery SignedSupport CircleUniform
open ExceptionalCountArithmetic ExceptionalProbability ObstructionProbability
open scoped ENNReal
namespace DeletionCode.PaperProbability
theorem _root_.solution (t : ℕ) (ht : 2 ≤ t) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ Q : ℕ,
      8 * ObstructionBound.scale t n (PaperParameters.k n) ≤ Q → ∀ x : Bits n,
        KUnique (padBits x) n (PaperParameters.k n) →
          realWeights (Gram (PaperParameters.L n)) (obstructionEvent t (PaperParameters.k n) Q x) ≤
            ENNReal.ofReal (1 / 12 : ℝ) := by
  filter_upwards [PaperParameters.eventually_ready (4 * t + 2)] with n hn
  intro Q hQ x hx
  exact ObstructionBound.obstruction_measure_le t (PaperParameters.k n) Q ht x hx (by omega) hn.2.2
    (PaperParameters.le_two_pow_of_L_lt n) hQ (labels_ge_two t n Q (by omega) hQ)
end DeletionCode.PaperProbability
