-- Prove2me | solution 1 for DeletionCode.CodeExistence.eventually_exists_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:42:14.028174+00:00
-- url     : https://prove2.me/submissions/eb284489-7ce1-45ab-8f3b-f1d2e9726b04

import Definitions.Def_DeletionCode_PaperProbability
import Definitions.Def_DeletionCode_FiniteDiscard
import Definitions.Def_DeletionCode_GoodWordBridge
import Definitions.Def_DeletionCode_RedundancyBounds
import Definitions.Def_DeletionCode_CodeExistence
import Theorems.Thm_DeletionCode_CodeExistence_exists_large_code
import Theorems.Thm_DeletionCode_PaperParameters_eventually_ready
import Theorems.Thm_DeletionCode_PaperParameters_threshold
import Theorems.Thm_DeletionCode_RedundancyBounds_code_nonempty
import Theorems.Thm_DeletionCode_RedundancyBounds_paper_redundancy_bound


set_option autoImplicit true
open DeletionCode DeletionCode.CodeExistence
open HeaderRecovery Windows SignedSupport CircleUniform CircleHash
open ExceptionalProbability ObstructionProbability CodeSelection
namespace DeletionCode.CodeExistence
theorem _root_.solution (t : ℕ) (ht : 2 ≤ t) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ C : Finset (Bits n),
      Corrects t C ∧ C.Nonempty ∧
      2 ^ n ≤ 8 * RedundancyBounds.labelCount t n * C.card ∧
      RedundancyBounds.redundancy n C ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
          ((6 * WitnessCost.exponent t + 6 : ℕ) : ℝ) *
            Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  filter_upwards [PaperParameters.eventually_ready (PaperProbability.threshold t),
    Filter.eventually_ge_atTop 4] with n hready hn
  obtain ⟨C, hcorrect, hcard⟩ := exists_large_code t n ht (by omega) hready.2.1 hready.2.2
  exact ⟨C, hcorrect, RedundancyBounds.code_nonempty n _ C hcard, hcard,
    RedundancyBounds.paper_redundancy_bound t n C hn hcard⟩
end DeletionCode.CodeExistence
