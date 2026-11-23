-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PermutationFixedPoints.two_mul_numDerangements_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:05:05.065813+00:00
-- url     : https://prove2.me/submissions/b1ec2e4f-0d19-42d7-9356-1f1eecc7b7ca

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_TwoMulNumDerangementsLeFactorial
import Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_two_mul_numDerangements_le_factorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.PermutationFixedPoints
namespace Formalism.CyclotomicNorms.PermutationFixedPoints
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) :
    2 * numDerangements k ≤ k.factorial := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact (two_mul_numDerangements_le_factorial m).1
end Formalism.CyclotomicNorms.PermutationFixedPoints
