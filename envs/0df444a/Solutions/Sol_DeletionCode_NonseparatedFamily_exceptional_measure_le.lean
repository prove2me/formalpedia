-- Prove2me | solution 1 for DeletionCode.NonseparatedFamily.exceptional_measure_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:16:07.666177+00:00
-- url     : https://prove2.me/submissions/05725b8b-ce1b-45ed-9159-0d6b685b0f97

import Definitions.Def_DeletionCode_ExceptionalPartnerCount
import Definitions.Def_DeletionCode_NonseparatedFamily
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans
import Theorems.Thm_DeletionCode_ExceptionalPartnerCount_candidatePartners_card_le
import Theorems.Thm_DeletionCode_ExceptionalProbability_exceptional_probability_le


set_option autoImplicit true
open DeletionCode DeletionCode.NonseparatedFamily
open MeasureTheory Windows HeaderRecovery SignedSupport CircleHash CircleUniform ConflictGraphWitness
open ExceptionalProbability ExceptionalPartnerCount ExceptionalCountArithmetic
namespace DeletionCode.NonseparatedFamily
theorem _root_.solution {n : ℕ} (t k Q : ℕ) (x : Bits n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k ≤ n) (hQ : 2 ≤ Q) :
    realWeights (Gram (windowLength k)) (exceptionalEvent t k Q x) ≤
      (exceptionalConstant t * windowLength k * n ^ (2 * t - 1) : ℕ) *
        ENNReal.ofReal (2 / (Q : ℝ)) := by
  have hn' : 1 ≤ n := by unfold windowLength at hn; omega
  have hc : ((candidatePartners t k x).card : ENNReal) ≤
      (exceptionalConstant t * windowLength k * n ^ (2 * t - 1) : ℕ) := by
    exact_mod_cast candidatePartners_card_le t k x hn'
  exact (exceptional_probability_le t k Q x hx hn hQ).trans
    (mul_le_mul hc le_rfl (by positivity) (by positivity))
end DeletionCode.NonseparatedFamily
