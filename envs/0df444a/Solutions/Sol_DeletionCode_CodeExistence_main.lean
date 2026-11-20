-- Prove2me | solution 1 for DeletionCode.CodeExistence.main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:48:24.615213+00:00
-- url     : https://prove2.me/submissions/58b2076d-939f-49dc-b9ea-949b0f4d12b3

import Definitions.Def_DeletionCode_PaperProbability
import Definitions.Def_DeletionCode_FiniteDiscard
import Definitions.Def_DeletionCode_GoodWordBridge
import Definitions.Def_DeletionCode_RedundancyBounds
import Definitions.Def_DeletionCode_CodeExistence
import Theorems.Thm_DeletionCode_CodeExistence_eventually_exists_code

set_option autoImplicit true
open DeletionCode DeletionCode.CodeExistence
open HeaderRecovery Windows SignedSupport CircleUniform CircleHash
open ExceptionalProbability ObstructionProbability CodeSelection
namespace DeletionCode.CodeExistence
theorem _root_.solution (t : ℕ) (ht : 2 ≤ t) :
    ∃ K : ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∃ C : Finset (Bits n),
      Corrects t C ∧ C.Nonempty ∧
      RedundancyBounds.redundancy n C ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
          (K : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  refine ⟨6 * WitnessCost.exponent t + 6, ?_⟩
  filter_upwards [eventually_exists_code t ht] with n hn
  obtain ⟨C, hc, hne, _hcard, hred⟩ := hn
  exact ⟨C, hc, hne, hred⟩
end DeletionCode.CodeExistence
