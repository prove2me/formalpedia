-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PermutationFixedPoints.two_mul_numDerangements_le_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:48.31334+00:00
-- url     : https://prove2.me/submissions/ade128fa-b675-40d7-9cc8-140ce91c7d3d

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_TwoMulNumDerangementsLeFactorial

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
theorem _root_.solution (m : ℕ) :
    2 * numDerangements (m + 1) ≤ (m + 1).factorial ∧
      2 * numDerangements (m + 2) ≤ (m + 2).factorial := by
  induction m with
  | zero => decide
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    show 2 * numDerangements (m + 3) ≤ (m + 3).factorial
    have e : numDerangements (m + 3) =
        (m + 2) * (numDerangements (m + 1) + numDerangements (m + 2)) :=
      numDerangements_add_two (m + 1)
    have hf2 : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ _
    have hf3 : (m + 3).factorial = (m + 3) * (m + 2).factorial := Nat.factorial_succ _
    rw [e, hf3, hf2]
    rw [hf2] at h2
    have k1 := Nat.mul_le_mul_left (m + 2) h1
    have k2 := Nat.mul_le_mul_left (m + 2) h2
    nlinarith
end Formalism.CyclotomicNorms.PermutationFixedPoints
